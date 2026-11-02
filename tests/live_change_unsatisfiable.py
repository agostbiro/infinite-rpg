#!/usr/bin/env python3
"""Test that a live change the server cannot satisfy always ends.

For each case, the test writes recorded replies (RPG_FAKE_API) that can never pass, starts a
fresh server on its own port, starts the built-in Adventure, and asks for a change. It checks that:

- the change ends within a fixed time,
- the last state is "failed" or "refused", with a last step that says why,
- the game is unchanged,
- the Player can play on, and can ask again ("Try again", then Cancel).

A last case does the same for a Wish whose replies never parse.

Build first with `lake build rpg`. Run from the repository folder:
    python3 tests/live_change_unsatisfiable.py [PORT]
The default port is 8097. The test stops every server it starts.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

# Do not leave a __pycache__ folder in the repository.
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "fake-api"))
from make_fixtures import stream  # noqa: E402

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8097
BASE = f"http://127.0.0.1:{PORT}"
# `RPG_BINARY` can name another build of the server, such as an older one.
BINARY = os.environ.get("RPG_BINARY", os.path.join(".lake", "build", "bin", "rpg"))
# The most proposals for one change (`maxChangeCalls` in Main.lean).
MAX_CALLS = 6


def request(path, body=None):
    """Send a GET (no body) or a POST (a JSON body). Returns the status and the JSON view."""
    data = None if body is None else json.dumps(body).encode()
    req = Request(BASE + path, data=data, headers={"Content-Type": "application/json"})
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


def wait_ended(seconds):
    """Poll until the DM stops. Returns the last view and the time it took."""
    started = time.monotonic()
    while time.monotonic() - started < seconds:
        _, view = request("/api/view")
        if view["generation"]["state"] != "running":
            return view, time.monotonic() - started
        time.sleep(0.25)
    raise AssertionError(f"The DM did not stop within {seconds} seconds")


class Server:
    """A fresh test server that reads recorded replies from `folder`."""

    def __init__(self, folder, limit_ms=None):
        env = dict(os.environ, RPG_FAKE_API=folder)
        env.pop("ANTHROPIC_API_KEY", None)
        if limit_ms is not None:
            env["RPG_CHANGE_LIMIT_MS"] = str(limit_ms)
        self.log = tempfile.TemporaryFile()
        self.proc = subprocess.Popen([BINARY, "--port", str(PORT), "--seed", "7"], env=env,
                                     stdout=self.log, stderr=subprocess.STDOUT)

    def __enter__(self):
        deadline = time.monotonic() + 60
        while time.monotonic() < deadline:
            if self.proc.poll() is not None:
                self.log.seek(0)
                raise AssertionError("The server stopped: " + self.log.read().decode())
            try:
                request("/api/view")
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


def proposals(view):
    """The highest proposal number in the steps of a change."""
    numbers = [int(n) for s in view["generation"]["steps"] for n in re.findall(r"proposal (\d+)", s["text"])]
    return max(numbers, default=0)


def run_change_case(name, files, state, text, error, most, limit_ms):
    with tempfile.TemporaryDirectory() as folder:
        for fixture, body in files.items():
            with open(os.path.join(folder, fixture + ".sse"), "w") as f:
                f.write(body)
        with Server(folder, limit_ms):
            code, before = request("/api/input", "begin")
            assert code == 200 and before["canChange"], (name, before.get("error"))
            code, working = request("/api/change", {"wish": "Make me unkillable"})
            assert code == 200 and working["generation"]["state"] == "running", name
            # Each proposal waits 1.5 seconds for its recorded reply, so 6 proposals take about 10.
            bound = 4 if limit_ms else 60
            view, took = wait_ended(bound)
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

            # The Player can play on. The failed change stays on screen until Dismiss.
            code, moved = request("/api/input", before["inputs"][0])
            assert code == 200 and len(moved["reports"]) > len(before["reports"]), name
            assert moved["generation"]["state"] == state, name
            # The Player can ask again, and Cancel leaves the game as it was.
            code, again = request("/api/retry", {})
            assert code == 200 and again["generation"]["state"] == "running", (name, again.get("error"))
            code, canceled = request("/api/cancel", {})
            assert code == 200 and canceled["generation"]["state"] == "idle", name
            assert checkpoint(canceled) == checkpoint(moved), f"{name}: Cancel changed the game"
            print(f"PASS {name}: {state} after {took:.1f}s and {proposals(view)} proposals: {last[:90]}")


def run_wish_case():
    """A Wish whose replies never parse fails after its 3 tries, and the title screen stays."""
    name = "a Wish whose replies never parse"
    with tempfile.TemporaryDirectory() as folder:
        for attempt in (1, 2, 3):
            with open(os.path.join(folder, f"adventure-{attempt}.sse"), "w") as f:
                f.write(stream("Here is a lovely Adventure, told in prose and not in JSON."))
        with Server(folder):
            _, before = request("/api/view")
            code, _ = request("/api/wish", {"wish": "A quiet walk in the Shire"})
            assert code == 200, name
            view, took = wait_ended(30)
            gen = view["generation"]
            assert gen["state"] == "failed", (name, gen)
            assert "in 3 tries" in gen["steps"][-1]["text"], (name, gen["steps"][-1])
            assert view["phase"] == "title" and view["seed"] == before["seed"], name
            print(f"PASS {name}: failed after {took:.1f}s: {gen['steps'][-1]['text']}")


def main():
    assert os.path.exists(BINARY), "Build first: lake build rpg"
    for case in CASES:
        run_change_case(*case)
    run_wish_case()
    print("PASS: every unsatisfiable request ended, said why, and left the game unchanged")


if __name__ == "__main__":
    main()
