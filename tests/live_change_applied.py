#!/usr/bin/env python3
"""Test that an admitted live change tells the Player what it put in play.

The test writes a recorded reply (RPG_FAKE_API) that grants Lafayette a Laser Sabre in the built-in
Adventure, starts a fresh server, and asks for the change. It checks that:

- the change passes the checks and the server installs it,
- the last Report is a `changeApplied` note with the wish, the new weapon, its kind and numbers,
  the weapon it replaces, and the counter-rules that are now in force,
- the Character panel names the new weapon and its kind,
- each rule in `worldRules` says where it comes from,
- the earlier Reports stay, and play goes on after the change.

Build first with `lake build rpg`. Run from the repository folder:
    python3 tests/live_change_applied.py [PORT]
The default port is 8098. The test stops the server it starts.
"""
import json
import os
import sys
import tempfile

# Do not leave a __pycache__ folder in the repository.
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "fake-api"))
from make_fixtures import stream, LASER_SABRE, LASER_SABRE_WISH  # noqa: E402
import live_change_unsatisfiable as server  # noqa: E402


def main():
    server.PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8098
    server.BASE = f"http://127.0.0.1:{server.PORT}"
    assert os.path.exists(server.BINARY), "Build first: lake build rpg"
    with tempfile.TemporaryDirectory() as folder:
        with open(os.path.join(folder, "change.sse"), "w") as f:
            f.write(stream(json.dumps(LASER_SABRE)))
        with server.Server(folder):
            code, before = server.request("/api/input", "begin")
            assert code == 200 and before["canChange"], before.get("error")
            assert before["character"]["weaponKind"] == "broadsword"
            assert all(r["origin"] == "adventure" for r in before["worldRules"])
            code, _ = server.request("/api/change", {"wish": LASER_SABRE_WISH})
            assert code == 200
            view, took = server.wait_ended(60)
            gen = view["generation"]
            assert gen["state"] == "idle", gen

            # The earlier Reports stay. The new last Report is the note of the change.
            assert view["reports"][:-1] == before["reports"]
            note = view["reports"][-1]["changeApplied"]
            assert note["wish"] == LASER_SABRE_WISH
            assert note["summary"] == LASER_SABRE["summary"]
            assert note["moment"] == LASER_SABRE["moment"]
            gear = note["equipment"]
            assert gear["name"] == "Laser Sabre" and gear["kind"] == "broadsword", gear
            assert gear["damage"] == "2d+1 cutting" and gear["attack"] == 14, gear
            assert gear["was"]["name"] == before["character"]["weapon"], gear
            assert gear["was"]["damage"] == before["character"]["damage"], gear
            assert gear["was"]["attack"] == before["character"]["attack"], gear
            assert note["requested"] == [] and note["scenes"] == 0, note
            # The counter-rules in the note are the ones in force, as tuned by the server.
            assert [r["name"] for r in note["counter"]] == ["Rallying Redcoats"], note

            # The Character panel shows the new weapon and its kind.
            hero = view["character"]
            assert hero["weapon"] == "Laser Sabre" and hero["weaponKind"] == "broadsword", hero
            assert hero["damage"] == "2d+1 cutting" and hero["attack"] == 14, hero
            for key in ("hp", "maxHP", "name", "st", "dx", "skills", "armor"):
                assert hero[key] == before["character"][key], key

            # Each rule says where it comes from.
            old = len(before["worldRules"])
            assert view["worldRules"][:old] == before["worldRules"]
            added = view["worldRules"][old:]
            assert [r["origin"] for r in added] == ["counter"], added
            assert [{k: v for k, v in r.items() if k != "origin"} for r in added] == note["counter"]

            # Play goes on. The note stays in the Reports.
            code, moved = server.request("/api/input", view["inputs"][0])
            assert code == 200 and len(moved["reports"]) > len(view["reports"])
            assert moved["reports"][:len(view["reports"])] == view["reports"]
            print(f"PASS: the Laser Sabre change was installed after {took:.1f}s, and its note says what is in play")


if __name__ == "__main__":
    main()
