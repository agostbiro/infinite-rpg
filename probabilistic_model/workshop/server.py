#!/usr/bin/env python3
"""One loopback-only site for generation, Lean certificates and graph play."""
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from fractions import Fraction as Q
from urllib.parse import urlparse
import hashlib
import json
import math
import secrets
import subprocess
import threading
import time
import uuid
import argparse
import socketserver

import engine
import certificate
import rules
import scenes
import copy

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parent
GENERATED = ROOT / "generated"
GENERATED.mkdir(exist_ok=True)
JOBS = {}
LOCK = threading.RLock()
VERIFY_LOCK = threading.Lock()
RNG = secrets.SystemRandom()


def sample(row):
    denominator = math.lcm(*(p.denominator for p in row.values()))
    roll = RNG.randrange(denominator)
    for value, p in row.items():
        roll -= p.numerator * (denominator // p.denominator)
        if roll < 0:
            return value
    raise RuntimeError("Invalid probability row.")


def job_view(job):
    fields = ("id", "status", "stage", "document", "error", "log", "generation_seconds",
              "verification_seconds", "current", "revision", "fight", "history", "source_hash",
              "timestamp", "change", "certificate_id")
    return {k: job[k] for k in fields if k in job}


def run_generation(job, body):
    started = time.perf_counter()
    try:
        document, world, ref, duel = engine.generate(
            difficulty=body.get("difficulty", "easy"), branches=body.get("branches", 2),
            max_nodes=body.get("max_nodes", 24), character_count=body.get("character_count", 4))
        source = certificate.export(document, world, ref, duel)
        source_path = GENERATED / (job["id"] + ".lean")
        source_path.write_text(source)
        payload_path = GENERATED / (job["id"] + ".json")
        payload_path.write_text(json.dumps(document, indent=2))
        with LOCK:
            job.update(document=document, world=world, ref=ref, duel=duel, status="verifying",
                       stage="Waiting for the Lean kernel", current=0, revision=0, fight=None, timestamp=0, certificate_id=job["id"],
                       history=[], source_hash=hashlib.sha256(source.encode()).hexdigest(),
                       generation_seconds=time.perf_counter() - started)
        with VERIFY_LOCK:
            with LOCK:
                job["stage"] = "Lean is checking mechanics, exact outcomes and fairness"
            verify_started = time.perf_counter()
            result = subprocess.run(["lake", "env", "lean", str(source_path)], cwd=PROJECT,
                                    capture_output=True, text=True, timeout=240)
            log = result.stdout + result.stderr
            # Require successful kernel elaboration and the complete requested proof set.
            required = ("generation_size", "character_coverage", "combat_mechanics", "exit_exact", "world_terminates", "loss_exact",
                        "bernoulli_fair", "phase_type_fair", "initial_timestamp_fair", "timestamp_fair",
                        "additional_properties", "actions_match_graph", "combat_outputs")
            required += scenes.PROOF_NAMES
            required += tuple(f"{prefix}_{n['id']}" for n in document['nodes'] if 'combat' in n
                              for prefix in ('collapsed_combat','combat_balanced'))
            accepted = result.returncode == 0 and all(f"WorkshopCertificate.{name}" in log for name in required)
            accepted = accepted and not any(x in log for x in ("sorryAx", "Lean.ofReduceBool", "uses `sorry`"))
            (GENERATED / (job["id"] + ".log")).write_text(log)
            with LOCK:
                job.update(verification_seconds=time.perf_counter() - verify_started,
                           log=log[-24000:], status="verified" if accepted else "rejected",
                           stage="All certificates accepted" if accepted else "Lean rejected the candidate")
                if not accepted:
                    job["error"] = "This candidate cannot be played: its Lean certificate was not accepted."
                persist(job)
    except subprocess.TimeoutExpired:
        with LOCK:
            job.update(status="rejected", stage="Verification timed out",
                       error="Lean exceeded the four-minute limit. The game remains locked.")
    except Exception as exc:
        with LOCK:
            job.update(status="rejected", stage="Generation stopped", error=str(exc))


def do_action(job, body):
    if job.get("change", {}).get("status") in ("searching", "verifying"):
        raise ValueError("Wait for the current rule change to finish.")
    if job["status"] != "verified":
        raise ValueError("Play is enabled only after Lean accepts the certificate.")
    if body.get("revision") != job["revision"]:
        raise ValueError("The game has advanced. Refresh this view before choosing again.")
    world = job["world"]
    mode = body.get("mode", "choice")
    log = ""
    if mode == "restart":
        job.update(current=job["document"].get("first_state",0), fight=None, history=[],
                   timestamp=job["document"].get("timestamp",0))
        log = "Returned to the last certified checkpoint."
    elif mode == "startCombat":
        node = world["nodes"][job["current"]]
        if "combat" not in node or job["fight"] is not None:
            raise ValueError("There is no new combat to enter here.")
        job["fight"] = node["combat"]["entry"]
        log = "Combat started at the character's current HP."
    elif job["fight"] is not None:
        state = job["fight"]
        options = job["duel"]["actions"][state]
        label = RNG.choice(list(options)) if mode == "uniform" else body.get("action")
        if label not in options:
            raise ValueError("That combat action is not available.")
        next_state = sample(options[label])
        before, after = engine.decode(state), engine.decode(next_state)
        actor = "Hero" if before[2] == 0 else "Opponent"
        log = f"{actor}: {label}. HP {before[0]}/{before[1]} → {after[0]}/{after[1]}."
        job["fight"] = next_state
        if job["duel"]["terminal"][next_state]:
            hp = job["duel"]["outputs"][next_state]
            destination = next(v for v in world["rows"][job["current"]] if world["nodes"][v]["hp"] == hp)
            job["current"] = destination
            job["timestamp"] = job.get("timestamp",0) + 1
            job["fight"] = None
            log += " Combat ended; its actual exit HP was carried into the game graph."
    else:
        state = job["current"]
        if world["terminal"][state]:
            raise ValueError("This path has reached an output. Restart to explore again.")
        options = world["choices"][state]
        label = RNG.choice(list(options)) if mode == "uniform" else body.get("action")
        if label not in options:
            raise ValueError("That choice is not available at the current event.")
        destination = sample(options[label])
        job["current"] = destination
        job["timestamp"] = job.get("timestamp",0) + 1
        log = f"{label} → {world['nodes'][destination]['title']} (HP {world['nodes'][destination]['hp']})."
    job["revision"] += 1
    job["history"].append(log)
    job["history"] = job["history"][-80:]
    persist(job)
    return job_view(job)


def encode_saved(value):
    if isinstance(value,Q): return {"$q":[value.numerator,value.denominator]}
    if isinstance(value,dict): return {"$map":[[encode_saved(k),encode_saved(v)] for k,v in value.items()]}
    if isinstance(value,(list,tuple)): return [encode_saved(v) for v in value]
    return value


def decode_saved(value):
    if isinstance(value,list): return [decode_saved(v) for v in value]
    if isinstance(value,dict):
        if "$q" in value: return Q(*value["$q"])
        return {decode_saved(k):decode_saved(v) for k,v in value["$map"]}
    return value


def persist(job):
    # Only completed verified sessions are durable. No Python object loading.
    if job.get("status")!="verified" or "id" not in job: return
    path=GENERATED/(job["id"]+".session.json")
    temp=path.with_suffix(".tmp")
    temp.write_text(json.dumps(encode_saved(job)))
    temp.replace(path)


def restore_sessions():
    for path in GENERATED.glob("*.session.json"):
        try:
            job=decode_saved(json.loads(path.read_text()))
            if job.get("status")!="verified": continue
            if job.get("change",{}).get("status") in ("searching","verifying"):
                job["change"]={"status":"rejected","message":"The server restarted during verification. Current game preserved."}
            JOBS[job["id"]]=job
        except (ValueError,KeyError,TypeError):
            continue


def start_change(job,body):
    if job.get("status")!="verified":
        raise ValueError("Generate and verify a graph first.")
    if body.get("revision")!=job["revision"]:
        raise ValueError("The game has advanced. Refresh before changing a rule.")
    if job["fight"] is not None:
        raise ValueError("Finish the current combat before changing rules.")
    if job.get("change",{}).get("status") in ("searching","verifying"):
        raise ValueError("A rule change is already being checked.")
    if job['world']['terminal'][job['current']]:
        raise ValueError("The game has ended. Restart the checkpoint or generate a new graph.")
    if sum(j.get('status') in ('generating','verifying') or j.get('change',{}).get('status') in ('searching','verifying') for j in JOBS.values()) >= 2:
        raise ValueError('Two verifications are already active. Please wait.')
    snapshot=copy.deepcopy({k:job[k] for k in ('world','ref','duel','document','current','fight','revision','timestamp')})
    change_id=uuid.uuid4().hex
    job['change']=dict(id=change_id,status='searching',message='Searching for an exact compensation…')
    threading.Thread(target=run_change,args=(job,snapshot,body,change_id),daemon=True).start()


def run_change(job,snapshot,body,change_id):
    started=time.perf_counter()
    try:
        document,world,ref,duel=rules.propose(snapshot,body)
        source=certificate.export(document,world,ref,duel,previous=snapshot)
        source_path=GENERATED/(change_id+'.lean')
        source_path.write_text(source)
        (GENERATED/(change_id+'.json')).write_text(json.dumps(document,indent=2))
        search_seconds=time.perf_counter()-started
        with LOCK:
            job['change'].update(status='verifying',message='Compensation found. Checking the new graph in Lean…',
                compensation=document['compensation'],search_seconds=search_seconds)
        with VERIFY_LOCK:
            verify_started=time.perf_counter()
            result=subprocess.run(['lake','env','lean',str(source_path)],cwd=PROJECT,
                                  capture_output=True,text=True,timeout=240)
            log=result.stdout+result.stderr
        (GENERATED/(change_id+'.log')).write_text(log)
        required=('combat_mechanics','combat_outputs','exit_exact','world_terminates','loss_exact',
                  'bernoulli_fair','timestamp_fair','additional_properties','actions_match_graph',
                  'rule_admitted','player_patch_exact','session_preserved','node_states_preserved',
                  'actual_player_input','combat_uses_actual_player','characters_well_formed','rule_scope')
        required += scenes.PROOF_NAMES
        required += tuple(f"{prefix}_{n['id']}" for n in document['nodes'] if 'combat' in n
                          for prefix in ('collapsed_combat','combat_balanced'))
        accepted=result.returncode==0 and all('WorkshopCertificate.'+name in log for name in required)
        accepted=accepted and not any(x in log for x in ('sorryAx','Lean.ofReduceBool','uses `sorry`'))
        if not accepted:
            raise ValueError('Lean rejected the proposed change. Current game preserved.')
        with LOCK:
            if job['revision']!=snapshot['revision'] or job['current']!=snapshot['current'] or job['fight'] is not None:
                raise ValueError('The game changed during verification. Candidate discarded.')
            staged=copy.deepcopy(job)
            staged.setdefault('certificate_history',[]).append(job.get('certificate_id',job['id']))
            staged.update(document=document,world=world,ref=ref,duel=duel,source_hash=hashlib.sha256(source.encode()).hexdigest(),
                       certificate_id=change_id,revision=job['revision']+1,log=log[-24000:],
                       generation_seconds=search_seconds,verification_seconds=time.perf_counter()-verify_started,
                       stage='Rule change verified and applied')
            staged['change'].update(status='applied',message='Verified and applied. Position, HP and event time preserved.',
                compensation=document['compensation'],seconds=time.perf_counter()-started)
            staged['history'].append(document['compensation'])
            persist(staged)
            job.clear()
            job.update(staged)
    except Exception as exc:
        with LOCK:
            if job.get('change',{}).get('id')==change_id:
                job['change'].update(status='rejected',message=str(exc),seconds=time.perf_counter()-started)
                persist(job)


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *_):
        pass

    def respond(self, code, data, content_type="application/json; charset=utf-8"):
        raw = json.dumps(data).encode() if content_type.startswith("application/json") else data
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(raw)

    def do_GET(self):
        path = urlparse(self.path).path
        if path == "/api/health":
            return self.respond(200, {"app": "MarkovRPG Graph Workshop", "version": 4, "project": str(PROJECT)})
        if path.startswith("/api/jobs/"):
            job_id = path.rsplit("/", 1)[-1]
            with LOCK:
                job = JOBS.get(job_id)
                data = job_view(job) if job else None
            return self.respond(200 if data else 404, data or {"error": "Unknown generation."})
        if path.startswith("/api/combat/"):
            job_id = path.rsplit("/", 1)[-1]
            with LOCK:
                job = JOBS.get(job_id)
                if not job or "document" not in job:
                    return self.respond(404, {"error": "Unknown game."})
                params = dict(p.split("=", 1) for p in urlparse(self.path).query.split("&") if "=" in p)
                entry = int(params.get("entry", job["fight"] if job["fight"] is not None else 0))
                if not 0 <= entry < 64:
                    return self.respond(400, {"error": "Invalid combat state."})
                c=job["duel"]
                data = engine.combat_view(c["level"], entry, c["hero_level"], c["hero_weapon"], c["enemy_weapon"])
            return self.respond(200, data)
        if path.startswith("/download/"):
            name = path.rsplit("/", 1)[-1]
            stem, _, extension = name.rpartition(".")
            if stem not in {k for j in JOBS.values() for k in [j["id"],j.get("certificate_id")] + j.get("certificate_history",[])} or extension not in ("lean", "json", "log"):
                return self.respond(404, {"error": "Unknown artifact."})
            f = GENERATED / name
            if not f.is_file():
                return self.respond(404, {"error": "Artifact not ready."})
            return self.respond(200, f.read_bytes(), "text/plain; charset=utf-8")
        assets = {"/": ("index.html", "text/html"), "/app.js": ("app.js", "text/javascript"),
                  "/style.css": ("style.css", "text/css")}
        if path in assets:
            name, content_type = assets[path]
            return self.respond(200, (ROOT / name).read_bytes(), content_type + "; charset=utf-8")
        self.respond(404, {"error": "Not found."})

    def do_POST(self):
        origin = self.headers.get("Origin")
        host = self.headers.get("Host")
        if origin and origin not in ("http://" + host, "https://" + host):
            return self.respond(403, {"error": "Cross-origin requests are not accepted."})
        try:
            size = int(self.headers.get("Content-Length", "0"))
            if not 0 < size <= 10000:
                raise ValueError("Invalid request size.")
            body = json.loads(self.rfile.read(size))
            if self.path == "/api/generate":
                with LOCK:
                    if sum(j["status"] in ("generating", "verifying") or j.get("change",{}).get("status") in ("searching","verifying") for j in JOBS.values()) >= 2:
                        return self.respond(429, {"error": "A verification is already queued. Please wait."})
                    job = {"id": uuid.uuid4().hex, "status": "generating", "stage": "Building exact state graphs"}
                    JOBS[job["id"]] = job
                threading.Thread(target=run_generation, args=(job, body), daemon=True).start()
                return self.respond(202, job_view(job))
            if self.path == "/api/rules":
                with LOCK:
                    job = JOBS.get(body.get("id"))
                    if not job:
                        raise ValueError("Unknown game.")
                    start_change(job,body)
                    result=job_view(job)
                return self.respond(202,result)
            if self.path == "/api/action":
                with LOCK:
                    job = JOBS.get(body.get("id"))
                    if not job:
                        raise ValueError("Unknown game.")
                    result = do_action(job, body)
                return self.respond(200, result)
            self.respond(404, {"error": "Not found."})
        except (ValueError, KeyError, StopIteration) as exc:
            self.respond(400, {"error": str(exc) or "Invalid action."})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=8093)
    parser.add_argument("--unix-socket", help="Private test socket; opens no TCP port")
    args = parser.parse_args()
    restore_sessions()
    if args.unix_socket:
        socket_path = Path(args.unix_socket)
        if socket_path.exists():
            raise SystemExit("Test socket already exists.")
        print(f"Private test socket: {socket_path}", flush=True)
        try:
            socketserver.ThreadingUnixStreamServer(str(socket_path), Handler).serve_forever()
        finally:
            socket_path.unlink(missing_ok=True)
    else:
        httpd = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
        print(f"Graph Workshop: http://127.0.0.1:{args.port}/", flush=True)
        httpd.serve_forever()
