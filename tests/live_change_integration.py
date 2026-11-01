#!/usr/bin/env python3
"""Exercise an isolated RPG_FAKE_API server, including rejection, cancellation, and admission.

Start it with: RPG_FAKE_API=tests/fake-api .lake/build/bin/rpg --port 8087 --seed 7
Run this test only against that disposable local session.
"""
import json
import sys
import time
from urllib.error import HTTPError
from urllib.request import Request, urlopen

BASE = sys.argv[1] if len(sys.argv) > 1 else "http://127.0.0.1:8087"


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
            ("seed", "adventure", "phase", "character", "scene", "fight", "map", "reports")}


def main():
    _, title = request("/api/view")
    assert title["phase"] == "title", "Use a fresh disposable test server"
    code, refused = request("/api/change", {"wish": "Give me a flamethrower now"})
    assert code == 409 and checkpoint(refused) == checkpoint(title)
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
        _, moved = request("/api/input", {"choose": {"choice": 1}})
        assert moved["scene"]["id"] == 2
        _, before = request("/api/input", {"choose": {"choice": 0}})
        assert before["scene"]["id"] == 5

    # The GM first wrongly calls the request unsupported. The server must ask it
    # to reconsider, then reject a missing counter-rule, then validate the real grant.
    code, _ = request("/api/change", {"wish": "Give me a flamethrower now"})
    assert code == 200
    saw_rejection = False
    saw_support_review = False
    saw_tuning = False
    started = time.monotonic()
    deadline = started + 30
    while time.monotonic() < deadline:
        _, view = request("/api/view")
        gen = view["generation"]
        if gen["state"] == "running":
            assert checkpoint(view) == checkpoint(before), "An unchecked proposal changed the game"
            saw_rejection |= any("Add a fun counter-rule" in error
                                 for step in gen["steps"] for error in step["errors"])
            saw_tuning |= any("Balancing the counter-rule" in step["text"] for step in gen["steps"])
            saw_support_review |= any("another way to make your mechanic work" in step["text"]
                                      for step in gen["steps"])
        else:
            assert gen["state"] == "idle", gen
            break
        time.sleep(0.3)
    else:
        raise AssertionError("Change did not finish within 30 seconds")
    if "--tuning" in sys.argv[2:]:
        assert saw_tuning, "An overpowered counter-rule was not locally screened"
        assert view["worldRules"][0]["hitBonus"] == 2
        assert view["worldRules"][0]["damageBonus"] == 3
        assert view["worldRules"][0]["armorBonus"] == 1
    assert saw_rejection
    assert saw_support_review, "The GM declined without reconsidering a supported mechanic"
    assert view["character"]["weapon"] == "Stormglass Flamethrower"
    assert view["character"]["damage"] == "3d burning"
    for key in ("hp", "maxHP", "name", "st", "dx", "iq", "ht", "skills", "armor"):
        assert view["character"][key] == before["character"][key], key
    assert view["scene"] == before["scene"] and view["map"] == before["map"]
    assert view["seed"] == before["seed"]
    assert view["reports"][:-1] == before["reports"]
    assert "worldRule" in view["reports"][-1]
    assert [r["name"] for r in view["worldRules"]] == ["Scorched Fury", "Cinder Veil"]

    # The first roll still uses the original game's seed: validation did not spend game dice.
    code, moved = request("/api/input", {"choose": {"choice": 1}})
    assert code == 200 and moved["scene"]["id"] == (6 if late else 2)
    roll = next(r["successRoll"]["roll"] for r in moved["reports"] if "successRoll" in r)
    assert roll["faces"] == [4, 1, 1]
    print(f"Rule change: {time.monotonic() - started:.2f}s; late checkpoint={late}")
    print("PASS: capability rejection reconsidered; illegal patch rejected; cancellation and admitted change preserve state and dice")


if __name__ == "__main__":
    main()
