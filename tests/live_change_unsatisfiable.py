#!/usr/bin/env python3
"""Test that a live change always ends, and that the paused-Fight check accepts a small Fight.

For each failure case, the test writes recorded replies (RPG_FAKE_API) that can never pass, starts a
fresh server on its own port, starts the built-in Adventure, and asks for a change. It checks that:

- the change ends within a fixed time,
- the last state is "failed" or "refused", with a last step that says why,
- the game is unchanged,
- the Player can play on, and can ask again ("Try again", then Cancel).

Four cases ask for the change during a Fight that is too large to check with the change. They also
check that the server never checks the same rules twice and spends no validation batch. In the first
case the last step names the paused Fight as the cause. The second case does the same, but each
proposal changes the text of a future Scene and keeps the combat rules. A third case changes only
the names, descriptions and order of the counter-rules in each proposal. In the fourth case the
screen fails, so the server tunes the counter-rules. A tuned variant that fails the paused-Fight
check is not picked again.

A last case does the same for a Wish whose replies never parse. One more case checks the other side:
the same flamethrower during a Fight against one wounded Grenadier passes the paused-Fight check
and is installed. It spends one validation batch, and the Fight keeps its HP, maneuvers and round.
In a last case a proposal passes the paused-Fight check and fails validation, and the next one
has the same effects with new wording and order. The server reuses the passed check: one paused
check and two validation batches.

The cases run at the same time, each with its own server on its own port.

Build first with `lake build rpg`. Run from the repository folder:
    python3 tests/live_change_unsatisfiable.py [PORT]
The cases use the ports from PORT (default 8100) up, one port for each case. The test stops every
server it starts.
"""
from concurrent.futures import ThreadPoolExecutor
import json
import os
import re
import socket
import subprocess
import sys
import tempfile
import time
import traceback
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

# Do not leave a __pycache__ folder in the repository.
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "fake-api"))
from make_fixtures import main as make_fixtures, stream  # noqa: E402

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8100
BASE = f"http://127.0.0.1:{PORT}"
# `RPG_BINARY` can name another build of the server, such as an older one.
BINARY = os.environ.get("RPG_BINARY", os.path.join(".lake", "build", "bin", "rpg"))
# The most proposals for one change (`maxChangeCalls` in Main.lean).
MAX_CALLS = 6
# The most tries for one Wish (`maxWishAttempts` in Main.lean).
MAX_WISH_ATTEMPTS = 5


def request(path, body=None, base=None):
    """Send a GET (no body) or a POST (a JSON body) to `base` (default BASE).
    Returns the status and the JSON view."""
    data = None if body is None else json.dumps(body).encode()
    req = Request((base or BASE) + path, data=data, headers={"Content-Type": "application/json"})
    try:
        with urlopen(req, timeout=20) as response:
            return response.status, json.load(response)
    except HTTPError as error:
        return error.code, json.load(error)


def checkpoint(view):
    """The parts of a view that a change must not touch when it fails."""
    return {key: view[key] for key in
            ("seed", "adventure", "phase", "character", "scene", "fight", "map", "reports",
             "environment", "worldRules")}


def wait_ended(seconds, base=None):
    """Poll until the DM stops. Returns the last view and the time it took."""
    started = time.monotonic()
    while time.monotonic() - started < seconds:
        _, view = request("/api/view", base=base)
        if view["generation"]["state"] != "running":
            return view, time.monotonic() - started
        time.sleep(0.25)
    raise AssertionError(f"The DM did not stop within {seconds} seconds")


class Server:
    """A fresh test server on `port` (default PORT) that reads recorded replies from `folder`."""

    def __init__(self, folder, limit_ms=None, port=None):
        port = port or PORT
        self.base = f"http://127.0.0.1:{port}"
        # Refuse a port that is in use, so the test never talks to another server.
        with socket.socket() as probe:
            if probe.connect_ex(("127.0.0.1", port)) == 0:
                raise AssertionError(f"Port {port} is in use. Pass another first port: PORT")
        env = dict(os.environ, RPG_FAKE_API=folder)
        env.pop("ANTHROPIC_API_KEY", None)
        if limit_ms is not None:
            env["RPG_CHANGE_LIMIT_MS"] = str(limit_ms)
        self.log = tempfile.TemporaryFile()
        self.proc = subprocess.Popen([BINARY, "--port", str(port), "--seed", "7"], env=env,
                                     stdout=self.log, stderr=subprocess.STDOUT)

    def __enter__(self):
        deadline = time.monotonic() + 60
        while time.monotonic() < deadline:
            if self.proc.poll() is not None:
                self.log.seek(0)
                raise AssertionError("The server stopped: " + self.log.read().decode())
            try:
                request("/api/view", base=self.base)
                return self
            except (URLError, ConnectionError):
                time.sleep(0.2)
        raise AssertionError("The server did not start")

    def __exit__(self, *exc):
        self.proc.terminate()
        try:
            self.proc.wait(10)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait()
        self.log.close()


# A change that makes the hero unkillable: it can never meet the death curve.
UNKILLABLE = {
    "supported": True,
    "summary": "No blade can wound you now, and your Godsteel Blade cuts through anything.",
    "moment": "Wounded foes make a Last Stand. Strike them down or guard.",
    "equipment": {"weapon": "broadsword", "name": "Godsteel Blade", "attackLevel": 18, "dice": 6, "add": 6},
    "requestedRules": [
        {"name": "Unkillable", "description": "You gain +4 to hit, +6 damage, and 4 armor, always.",
         "side": "hero", "trigger": "always", "hitBonus": 4, "damageBonus": 6, "armorBonus": 4}],
    "rules": [
        {"name": "Last Stand", "description": "Enemies at half HP or less gain +1 to hit.",
         "side": "foes", "trigger": "wounded", "hitBonus": 1, "damageBonus": 0, "armorBonus": 0}],
    "scenes": [],
}


def variant(**changes):
    """A copy of UNKILLABLE with some fields replaced."""
    out = json.loads(json.dumps(UNKILLABLE))
    out.update(changes)
    return out


# A different requested rule: the server must keep the gift of the first legal proposal.
DRIFTED = variant(requestedRules=[dict(UNKILLABLE["requestedRules"][0], name="Unbreakable", armorBonus=3)])
UNSUPPORTED_TEXT = "The rules cannot stop all damage, so I cannot make you immortal. Try heavy armor instead."
UNSUPPORTED = {"supported": False, "summary": UNSUPPORTED_TEXT, "moment": "", "equipment": None,
               "requestedRules": [], "rules": [], "scenes": []}

# Each case: a name, the recorded replies, the expected last state, a part of the last step's
# text, a part of one of its errors (or None for no check), the most proposals, and the test time
# limit of the change (or None for 3 minutes).
OUT_OF_BUDGET = "stopped after 6 proposals"
CASES = [
    ("unkillable hero, the same proposal every time",
     {"change": stream(json.dumps(UNKILLABLE))}, "failed", OUT_OF_BUDGET, "0 of 1200 games", MAX_CALLS, None),
    ("a reply that never parses",
     {"change": stream("Happy to help! Here is my idea, but not as JSON.")}, "failed", OUT_OF_BUDGET, "",
     MAX_CALLS, None),
    ("a reply that is always cut off",
     {"change": stream(json.dumps(UNKILLABLE)[:200], stop="max_tokens")}, "failed", OUT_OF_BUDGET,
     "The patch was cut off", MAX_CALLS, None),
    ("no counter-rule, every time",
     {"change": stream(json.dumps(variant(rules=[])))}, "failed", OUT_OF_BUDGET, "Add a fun counter-rule",
     MAX_CALLS, None),
    ("the gift changes after the first legal proposal",
     {"change-1": stream(json.dumps(UNKILLABLE)), "change": stream(json.dumps(DRIFTED))},
     "failed", OUT_OF_BUDGET, "Keep the requested equipment", MAX_CALLS, None),
    ("unsupported every time",
     {"change": stream(json.dumps(UNSUPPORTED))}, "refused", UNSUPPORTED_TEXT, None, 2, None),
    ("the API refuses",
     {"change": stream(None, stop="refusal")}, "refused", "cannot grant that request", None, 1, None),
    ("the API cannot be reached",
     {}, "failed", "could not be reached", "no recorded reply", 1, None),
    ("the time limit ends the change during a reply",
     {"change": stream(json.dumps(UNKILLABLE))}, "failed", "time limit of 2 seconds", None, MAX_CALLS, 2000),
]

# The Choices from the start, with seed 7, that lead to the Fight against Grenadier 1 and 2.
TWO_GRENADIERS = (1, 0, 0)
# The Choices from the start, with seed 7, that lead to the Fight against Grenadier 1 alone.
ONE_GRENADIER = (0, 0, 0, 0)
# Then All-Out Defense and Attack, with seed 7: in round 3, Grenadier 1 is alive with 7 of 11 HP.
WOUNDED_GRENADIER = ONE_GRENADIER + (2, 0)
# A flamethrower grant that passes the balance check (the last reply of the integration test).
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fake-api", "change-3.sse")) as f:
    FLAMETHROWER = f.read()
# The same grant with a counter-rule that is too strong, so the screen fails and the server tunes it
# (the last reply of the integration test with --tuning).
with tempfile.TemporaryDirectory() as _folder:
    make_fixtures(_folder, True)
    with open(os.path.join(_folder, "change-3.sse")) as f:
        STRONG_FLAMETHROWER = f.read()


def proposal_of(sse):
    """The JSON proposal in the text blocks of a recorded reply."""
    text = ""
    for line in sse.splitlines():
        if line.startswith("data: "):
            data = json.loads(line[6:])
            if data.get("type") == "content_block_delta" and data["delta"].get("type") == "text_delta":
                text += data["delta"]["text"]
    return json.loads(text)


def with_ending_text(proposal, n):
    """A copy of `proposal` that also replaces the text of the future ending, Scene 13, with
    version `n`. The combat rules stay the same."""
    out = json.loads(json.dumps(proposal))
    out["scenes"] = [{"id": 13, "title": "Ending: Cut Off", "choices": [],
                      "text": f"The dragoons cut off the rear guard. You get away across the river (version {n})."}]
    return out


# The flamethrower with a new ending text in each proposal: the same combat rules every time.
SCENE_EDITS = {f"change-{n}": stream(json.dumps(with_ending_text(proposal_of(FLAMETHROWER), n)))
               for n in range(1, MAX_CALLS + 1)}


def with_rule_wording(proposal, n):
    """A copy of `proposal` whose counter-rules have version `n` of their names and descriptions,
    in the other order when `n` is even. The sides, triggers and numbers stay the same."""
    out = json.loads(json.dumps(proposal))
    for rule in out["rules"]:
        rule["name"] = f"{rule['name']} (version {n})"
        rule["description"] = f"Version {n} of this rule: {rule['description']}"
    if n % 2 == 0:
        out["rules"].reverse()
    return out


assert len(proposal_of(FLAMETHROWER)["rules"]) >= 2, "The order change needs two counter-rules"
# The flamethrower with new wording and order of its counter-rules: the same combat rules.
WORDING_EDITS = {f"change-{n}": stream(json.dumps(with_rule_wording(proposal_of(FLAMETHROWER), n)))
                 for n in range(1, MAX_CALLS + 1)}
# Each case: the same fields as CASES, then the Choices that lead to the paused Fight.
PAUSED_CASES = [
    ("a flamethrower during a Fight against two Grenadiers, every time",
     {"change": FLAMETHROWER}, "failed", "The paused Fight could not be checked with the last one",
     "The paused Fight against Grenadier 1 and Grenadier 2 is over the solver's budget", MAX_CALLS, None,
     TWO_GRENADIERS),
    # Each proposal changes only a future Scene, so the paused-Fight check runs once.
    ("a flamethrower with a new ending text each time, during a Fight against two Grenadiers",
     SCENE_EDITS, "failed", "The paused Fight could not be checked with the last one",
     "The paused Fight against Grenadier 1 and Grenadier 2 is over the solver's budget", MAX_CALLS, None,
     TWO_GRENADIERS),
    # Each proposal changes only the names, descriptions and order of the counter-rules, so the
    # paused-Fight check runs once.
    ("a flamethrower with new counter-rule wording and order each time, during a Fight against two Grenadiers",
     WORDING_EDITS, "failed", "The paused Fight could not be checked with the last one",
     "The paused Fight against Grenadier 1 and Grenadier 2 is over the solver's budget", MAX_CALLS, None,
     TWO_GRENADIERS),
    # The first two proposals are tuned to two different variants, which fail the paused-Fight check.
    # After that, no variant that is left passes the screen, so the change ends with the balance rows.
    ("a flamethrower with a too strong counter-rule during a Fight against two Grenadiers",
     {"change": STRONG_FLAMETHROWER}, "failed", "could not find a balanced version", "the allowed range",
     MAX_CALLS, None, TWO_GRENADIERS),
]
TUNING = "Balancing the counter-rule"
CHECKED_RULES = "The checked counter-rules were: "
PAUSED_CHECK = "Checking that the paused Fight still ends"
CACHED = "These counter-rules already failed the paused-Fight check"
VALIDATION = "Checking a fresh validation batch"


def proposals(view):
    """The highest proposal number in the steps of a change."""
    numbers = [int(n) for s in view["generation"]["steps"] for n in re.findall(r"proposal (\d+)", s["text"])]
    return max(numbers, default=0)


def run_change_case(port, name, files, state, text, error, most, limit_ms, path=()):
    """Run one case of CASES on a fresh server on `port`. With `path`, make the Choices in `path`
    first, so that the change comes during a Fight. Then check that the Dungeon Master made all
    `most` proposals, that no rules were checked twice against the paused Fight, that a proposal
    sent again got the remembered rejection, and that no validation batch was spent."""
    with tempfile.TemporaryDirectory() as folder:
        for fixture, body in files.items():
            with open(os.path.join(folder, fixture + ".sse"), "w") as f:
                f.write(body)
        with Server(folder, limit_ms, port) as server:
            base = server.base
            code, before = request("/api/input", "begin", base)
            assert code == 200 and before["canChange"], (name, before.get("error"))
            for choice in path:
                code, before = request("/api/input", before["inputs"][choice], base)
                assert code == 200, name
            assert not path or (before["phase"] == "fight" and before["canChange"]), (name, before["phase"])
            code, working = request("/api/change", {"wish": "Make me unkillable"}, base)
            assert code == 200 and working["generation"]["state"] == "running", name
            # Each proposal waits 1.5 seconds for its recorded reply, so 6 proposals take about 10.
            # The other cases run at the same time and use the CPU, so the bound has a margin.
            bound = 8 if limit_ms else 60
            view, took = wait_ended(bound, base)
            gen = view["generation"]
            last = gen["steps"][-1]["text"] if gen["steps"] else ""
            assert gen["mode"] == "change", (name, gen)
            assert gen["state"] == state, (name, gen)
            assert text in last, (name, last)
            if error is not None:
                errors = gen["steps"][-1]["errors"]
                assert errors and any(error in e for e in errors), (name, errors)
            assert state == "refused" or "unchanged" in last, (name, last)
            assert 1 <= proposals(view) <= most, (name, proposals(view))
            assert checkpoint(view) == checkpoint(before), f"{name}: the game changed"
            if path:
                texts = [s["text"] for s in gen["steps"]]
                assert proposals(view) == most, (name, proposals(view))
                # Each check of the paused Fight reports the counter-rules it checked. No rules
                # are checked twice: a proposal sent again gets the remembered rejection, and the
                # tuning skips a variant that failed.
                checked = [e for step in gen["steps"] for e in step["errors"] if e.startswith(CHECKED_RULES)]
                assert checked and sum(PAUSED_CHECK in t for t in texts) == len(checked), (name, texts)
                assert len(set(checked)) == len(checked), (name, checked)
                if any(TUNING in t for t in texts):
                    # Each proposal is screened and tuned again; a new variant is checked each time.
                    assert len(checked) >= 2, (name, checked)
                else:
                    # The screen passes, so the proposal itself is checked once and then remembered.
                    assert len(checked) == 1, (name, checked)
                    first = next(i for i, t in enumerate(texts) if PAUSED_CHECK in t)
                    cached = [i for i, step in enumerate(gen["steps"]) if any(CACHED in e for e in step["errors"])]
                    assert len(cached) >= most - 1 and min(cached) > first, (name, cached, first)
                assert not any(VALIDATION in t for t in texts), (name, texts)
                # No validation batch spent a part of the error allowance.
                assert gen["changeChecks"] == before["generation"]["changeChecks"], (name, gen["changeChecks"])

            # The Player can play on. The failed change stays on screen until Dismiss.
            code, moved = request("/api/input", before["inputs"][0], base)
            assert code == 200 and len(moved["reports"]) > len(before["reports"]), name
            assert moved["generation"]["state"] == state, name
            # The Player can ask again, and Cancel leaves the game as it was.
            code, again = request("/api/retry", {}, base)
            assert code == 200 and again["generation"]["state"] == "running", (name, again.get("error"))
            code, canceled = request("/api/cancel", {}, base)
            assert code == 200 and canceled["generation"]["state"] == "idle", name
            assert checkpoint(canceled) == checkpoint(moved), f"{name}: Cancel changed the game"
            print(f"PASS {name}: {state} after {took:.1f}s and {proposals(view)} proposals: {last[:90]}")


def run_accept_case(port):
    """A change during a small Fight passes the paused-Fight check and is installed. It runs on a
    fresh server on `port`."""
    name = "a flamethrower during a Fight against one wounded Grenadier"
    with tempfile.TemporaryDirectory() as folder:
        with open(os.path.join(folder, "change.sse"), "w") as f:
            f.write(FLAMETHROWER)
        with Server(folder, port=port) as server:
            base = server.base
            code, before = request("/api/input", "begin", base)
            assert code == 200, name
            for choice in WOUNDED_GRENADIER:
                code, before = request("/api/input", before["inputs"][choice], base)
                assert code == 200, name
            assert before["phase"] == "fight" and before["canChange"], (name, before["phase"])
            foes = before["fight"]["foes"]
            assert [f["name"] for f in foes] == ["Grenadier 1"], name
            # The Grenadier is wounded, so the test sees it if the change heals it.
            assert foes[0]["alive"] and foes[0]["hp"] < foes[0]["maxHP"], (name, foes)
            code, working = request("/api/change", {"wish": "Give me a flamethrower now"}, base)
            assert code == 200 and working["generation"]["state"] == "running", name
            view, took = wait_ended(60, base)
            gen = view["generation"]
            assert gen["state"] == "idle", (name, gen)
            # One validation batch was spent, and the change was installed into the paused Fight.
            assert gen["changeChecks"] == before["generation"]["changeChecks"] + 1, (name, gen["changeChecks"])
            assert view["character"]["weapon"] == "Stormglass Flamethrower", (name, view["character"])
            assert "changeApplied" in view["reports"][-1], (name, view["reports"][-1])
            assert view["phase"] == "fight", (name, view["phase"])
            for key in ("hp", "maneuver", "alive"):
                assert [f[key] for f in view["fight"]["foes"]] == [f[key] for f in foes], (name, key)
            assert view["fight"]["round"] == before["fight"]["round"], name
            assert view["fight"]["hero"]["hp"] == before["fight"]["hero"]["hp"], name
            print(f"PASS {name}: installed after {took:.1f}s")


# A weaker flamethrower counter-rule. With seed 7, during the Fight against the wounded Grenadier,
# it passes the paused-Fight check and the screen, but fails the fresh validation batch. A search
# over the numbers of the two counter-rules found it; a change to the balance check can move it.
BORDERLINE = proposal_of(FLAMETHROWER)
BORDERLINE["rules"][0].update(hitBonus=1, damageBonus=1)
BORDERLINE["rules"][1].update(armorBonus=2)
REUSED = "The paused Fight already passed its check with these rules"


def run_reuse_case(port):
    """A proposal passes the paused-Fight check and fails validation. The next proposal has the same
    effects with new wording and order, so the server reuses the passed check and validates again.
    It runs on a fresh server on `port`."""
    name = "a reworded proposal after a failed validation, during a Fight against one wounded Grenadier"
    with tempfile.TemporaryDirectory() as folder:
        files = {"change-1": stream(json.dumps(BORDERLINE)),
                 "change-2": stream(json.dumps(with_rule_wording(BORDERLINE, 2))),
                 "change": stream("Not JSON, so the change ends after its last proposal.")}
        for fixture, body in files.items():
            with open(os.path.join(folder, fixture + ".sse"), "w") as f:
                f.write(body)
        with Server(folder, port=port) as server:
            base = server.base
            code, before = request("/api/input", "begin", base)
            assert code == 200, name
            for choice in WOUNDED_GRENADIER:
                code, before = request("/api/input", before["inputs"][choice], base)
                assert code == 200, name
            assert before["phase"] == "fight" and before["canChange"], (name, before["phase"])
            code, working = request("/api/change", {"wish": "Give me a flamethrower now"}, base)
            assert code == 200 and working["generation"]["state"] == "running", name
            view, took = wait_ended(60, base)
            gen = view["generation"]
            texts = [s["text"] for s in gen["steps"]]
            assert gen["state"] == "failed", (name, gen["state"], texts[-1:])
            assert not any(TUNING in t for t in texts), (name, texts)
            # The first proposal runs the paused-Fight check; the second reuses it.
            assert sum(PAUSED_CHECK in t for t in texts) == 1, (name, texts)
            assert sum(REUSED in t for t in texts) == 1, (name, texts)
            # Both proposals reach a fresh validation batch, and both fail it.
            assert sum(VALIDATION in t for t in texts) == 2, (name, texts)
            assert gen["changeChecks"] == before["generation"]["changeChecks"] + 2, (name, gen["changeChecks"])
            assert checkpoint(view) == checkpoint(before), f"{name}: the game changed"
            print(f"PASS {name}: one paused check, two validation batches, after {took:.1f}s")


def run_wish_case(port):
    """A Wish whose replies never parse fails after all its tries, and the title screen stays.
    It runs on a fresh server on `port`."""
    name = "a Wish whose replies never parse"
    with tempfile.TemporaryDirectory() as folder:
        for attempt in range(1, MAX_WISH_ATTEMPTS + 1):
            with open(os.path.join(folder, f"adventure-{attempt}.sse"), "w") as f:
                f.write(stream("Here is a lovely Adventure, told in prose and not in JSON."))
        with Server(folder, port=port) as server:
            base = server.base
            _, before = request("/api/view", base=base)
            code, _ = request("/api/wish", {"wish": "A quiet walk in the Shire"}, base)
            assert code == 200, name
            view, took = wait_ended(30, base)
            gen = view["generation"]
            assert gen["state"] == "failed", (name, gen)
            assert "five-attempt limit" in gen["steps"][-1]["text"], (name, gen["steps"][-1])
            assert view["phase"] == "title" and view["seed"] == before["seed"], name
            print(f"PASS {name}: failed after {took:.1f}s: {gen['steps'][-1]['text']}")


def main():
    assert os.path.exists(BINARY), "Build first: lake build rpg"
    # Each case waits for recorded replies most of the time, so the cases run at the same time.
    # Each one has its own server and port, and no case reads the state of another.
    cases = CASES + PAUSED_CASES
    jobs = [(case[0], lambda port=PORT + i, case=case: run_change_case(port, *case))
            for i, case in enumerate(cases)]
    jobs.append(("a Wish whose replies never parse", lambda port=PORT + len(cases): run_wish_case(port)))
    jobs.append(("a flamethrower during a Fight against one Grenadier",
                 lambda port=PORT + len(cases) + 1: run_accept_case(port)))
    jobs.append(("a reworded proposal after a failed validation",
                 lambda port=PORT + len(cases) + 2: run_reuse_case(port)))
    with ThreadPoolExecutor(max_workers=len(jobs)) as pool:
        futures = [(name, pool.submit(job)) for name, job in jobs]
    failures = [(name, f.exception()) for name, f in futures if f.exception() is not None]
    for name, failure in failures:
        print(f"FAIL {name}:\n" + "".join(traceback.format_exception(failure)), end="")
    if failures:
        sys.exit(1)
    print("PASS: every case passed: each failed request ended, said why, and left the game unchanged")


if __name__ == "__main__":
    main()
