#!/usr/bin/env python3
"""Test a live change on a fresh RPG_FAKE_API server: refusal, cancel, an illegal patch, and install.

The test starts from a Wish in test mode: the server reads the recorded reply adventure-N.sse.
If the folder has no recorded Wish, the server cannot make an Adventure, so the test prints SKIP
and stops with exit code 0. The follow-up in docs/follow-ups.md adds a recorded Wish back.

Start the server with: RPG_FAKE_API=tests/fake-api .lake/build/bin/rpg --port 8087 --seed 7
Then run: tests/live_change_integration.py http://127.0.0.1:8087 [--late] [--tuning]
Run this test only against that disposable local server: it makes and saves an Adventure.
"""
import json
import sys
import time
from urllib.error import HTTPError
from urllib.request import Request, urlopen

BASE = sys.argv[1] if len(sys.argv) > 1 else "http://127.0.0.1:8087"
MASK = (1 << 64) - 1


def request(path, body=None):
    data = None if body is None else json.dumps(body).encode()
    req = Request(BASE + path, data=data, headers={"Content-Type": "application/json"})
    try:
        with urlopen(req, timeout=20) as response:
            return response.status, json.load(response)
    except HTTPError as error:
        return error.code, json.load(error)


def checkpoint(view):
    return {key: view[key] for key in
            ("seed", "adventure", "phase", "character", "scene", "fight", "map", "reports", "environment")}


def wait_idle(seconds):
    """Poll until the DM stops. Returns the last view and every view seen while it ran."""
    deadline = time.monotonic() + seconds
    seen = []
    while time.monotonic() < deadline:
        _, view = request("/api/view")
        seen.append(view)
        if view["generation"]["state"] != "running":
            return view, seen
        time.sleep(0.3)
    raise AssertionError(f"The DM did not finish within {seconds} seconds")


def seeded_faces(seed, count):
    """The first `count` die faces from the game's dice (SplitMix64, as `Rng.next` in Rpg/Engine.lean)."""
    state = seed & MASK
    faces = []
    for _ in range(count):
        state = (state + 0x9E3779B97F4A7C15) & MASK
        z = state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        faces.append((z ^ (z >> 31)) % 6 + 1)
    return faces


def rolled_faces(reports):
    """Every die face that the Engine rolled, in order. A maxed damage roll rolls no dice."""
    faces = []
    for report in reports:
        if not isinstance(report, dict):
            continue
        kind, data = next(iter(report.items()))
        if kind in ("successRoll", "attack", "dodge"):
            faces += data["roll"]["faces"]
        elif kind == "damage" and not data["maxed"]:
            faces += data["faces"]
    return faces


def main():
    _, home = request("/api/view")
    assert home["phase"] == "title", "Use a fresh disposable test server"
    # With no Adventure loaded, a change and an input are both refused, and nothing changes.
    code, refused = request("/api/change", {"wish": "Give me a flamethrower now"})
    assert code == 409 and checkpoint(refused) == checkpoint(home)
    code, refused = request("/api/input", "begin")
    assert code == 400 and checkpoint(refused) == checkpoint(home)

    # Make an Adventure from a Wish, with the recorded replies.
    code, _ = request("/api/wish", {"wish": "I love LOTR, give me an adventure set in the Shire"})
    assert code == 200
    wished, _ = wait_idle(60)
    gen = wished["generation"]
    # Skip only when the first try has no recorded reply. A recorded Wish that fails its checks
    # and then has no recorded fix is a failure, not a skip.
    first_errors = next((s["errors"] for s in gen["steps"] if s["errors"]), [])
    if gen["state"] == "failed" and any("no recorded reply" in e for e in first_errors):
        print("SKIP: the test folder has no recorded Wish (adventure-1.sse), so no Adventure can start."
              " See docs/follow-ups.md: add back the fake-mode Wish.")
        return
    assert gen["state"] == "ready", gen
    code, title = request("/api/load", {"id": gen["readyId"]})
    assert code == 200 and title["phase"] == "title"
    code, before = request("/api/input", "begin")
    assert code == 200 and before["phase"] == "scene"

    # Cancellation before generation completes must preserve all game state.
    code, working = request("/api/change", {"wish": "Give me a flamethrower now"})
    assert code == 200 and working["generation"]["mode"] == "change"
    code, blocked = request("/api/input", {"choose": {"choice": 0}})
    assert code == 409 and checkpoint(blocked) == checkpoint(before)
    code, canceled = request("/api/cancel", {})
    assert code == 200 and checkpoint(canceled) == checkpoint(before)
    time.sleep(2)
    assert checkpoint(request("/api/view")[1]) == checkpoint(before), "Canceled work installed late"

    late = "--late" in sys.argv[2:]
    if late:
        # Move on up to two Choices, so the change comes at a later checkpoint.
        for _ in range(2):
            if before["phase"] != "scene" or not before["inputs"]:
                break
            code, before = request("/api/input", before["inputs"][0])
            assert code == 200
        assert len(before["reports"]) > 1 and before["phase"] in ("scene", "fight") and before["inputs"]

    # The GM first wrongly calls the request unsupported. The server must ask it
    # to reconsider, then reject a missing counter-rule, then validate the real grant.
    code, _ = request("/api/change", {"wish": "Give me a flamethrower now"})
    assert code == 200
    started = time.monotonic()
    view, seen = wait_idle(30)
    running = [v for v in seen if v["generation"]["state"] == "running"]
    for v in running:
        assert checkpoint(v) == checkpoint(before), "An unchecked proposal changed the game"
    steps = [s for v in running for s in v["generation"]["steps"]] + view["generation"]["steps"]
    saw_rejection = any("Add a fun counter-rule" in e for s in steps for e in s["errors"])
    saw_support_review = any("another way to make your mechanic work" in s["text"] for s in steps)
    assert view["generation"]["state"] == "idle", view["generation"]
    if "--tuning" in sys.argv[2:]:
        # The local balancing step can start and end between two polls, so check its result.
        tuned = next(r for r in view["worldRules"] if r["name"] == "Scorched Fury")
        assert tuned["hitBonus"] < 4 or tuned["damageBonus"] < 6 or tuned["armorBonus"] < 2, \
            "An overpowered counter-rule was not locally screened"
    assert saw_rejection
    assert saw_support_review, "The GM declined without reconsidering a supported mechanic"
    assert view["character"]["weapon"] == "Stormglass Flamethrower"
    assert view["character"]["damage"] == "3d burning"
    for key in ("hp", "maxHP", "name", "st", "dx", "iq", "ht", "skills", "armor"):
        assert view["character"][key] == before["character"][key], key
    assert view["scene"] == before["scene"] and view["map"] == before["map"]
    assert view["environment"] == before["environment"], "The change moved the world map"
    assert view["seed"] == before["seed"]
    assert view["reports"][:-1] == before["reports"]
    assert view["reports"][-1]["changeApplied"]["equipment"]["name"] == "Stormglass Flamethrower"
    assert view["worldRules"][:len(before["worldRules"])] == before["worldRules"]
    assert [r["name"] for r in view["worldRules"][len(before["worldRules"]):]] == ["Scorched Fury", "Cinder Veil"]

    # The game dice are the dice of the original seed: the checks did not spend them. Play on until
    # a die is rolled, then compare every face in the log with the seeded dice.
    moved = view
    for _ in range(20):
        if len(rolled_faces(moved["reports"])) > len(rolled_faces(before["reports"])) or not moved["inputs"]:
            break
        code, moved = request("/api/input", moved["inputs"][-1])
        assert code == 200
    faces = rolled_faces(moved["reports"])
    assert len(faces) > len(rolled_faces(before["reports"])), "No die was rolled after the change"
    assert faces == seeded_faces(moved["seed"], len(faces)), "The game dice changed"
    print(f"Rule change: {time.monotonic() - started:.2f}s; late checkpoint={late}")
    print("PASS: capability rejection reconsidered; illegal patch rejected; cancellation and admitted change preserve state and dice")


if __name__ == "__main__":
    main()
