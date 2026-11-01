#!/usr/bin/env python3
"""Assemble the locally authored campaign; no API call and no invented benchmark."""
import json
import time
import argparse
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Each main stage has its own place, incident and spatial action.
STAGES = json.loads((ROOT / "campaigns/napoleon-story-en.json").read_text())


def goto(text, target):
    return {"text": text, "outcome": {"type": "goto", "next": target}}


def assemble():
    hero = {
        "name": "Camille Laurent", "background": "An interpreter and cartographer with the expedition, you investigate with Salma to protect the water routes.",
        "st": 11, "dx": 12, "iq": 10, "ht": 12,
        "skills": [{"skill": s, "level": n} for s, n in [
            ("broadsword", 14), ("stealth", 13), ("lockpicking", 12),
            ("diplomacy", 11), ("brawling", 12), ("knife", 12)]],
        "weapon": "broadsword", "armor": "leather",
    }
    foe = {"name": "Armed Smuggler", "st": 14, "dx": 11, "iq": 9, "ht": 11,
           "skills": [{"skill": "knife", "level": 15}], "weapon": "largeKnife",
           "armor": "none", "naturalDR": 0}
    risky = {2, 4, 6, 8, 10, 12, 20, 28, 36, 44, 52, 60}
    scenes = []
    for i, (title, text, action) in enumerate(STAGES):
        chapter = ["I · The Stolen Maps", "II · The Nile Routes",
                   "III · The Cairo Evidence", "IV · Water at the Pyramids"][i // 16]
        choices = [goto(action, i + 1)]
        if i == 63:
            choices = [goto(action, 64), goto("Join Amina to maintain the water routes", 65)]
        elif i % 4 == 1:
            side = 100 + i
            choices.append(goto("Examine the objects and tracks nearby", side))
            scenes.append({
                "id": side, "title": title + " · The Detour",
                "text": text + " You take time to hear another witness and record the details. You can return to compare the evidence whenever you choose.",
                "choices": [
                    goto("Follow the path to continue the investigation", i + 1),
                    goto("Return along the survey route", max(0, i - 2)) if i > 1 else goto("Continue to the harbour", i + 1),
                ],
            })
        elif i not in risky:
            side = 200 + i
            choices.append({
                "text": "Examine the tracks quietly (Stealth)",
                "outcome": {"type": "roll", "against": "stealth", "modifier": 0,
                            "onSuccess": i + 1, "onFailure": side},
            })
            scenes.append({
                "id": side, "title": title + " · Another Lead",
                "text": "Your approach has drawn attention. Salma intervenes and gains time to explain the mission. You compare the accounts before continuing your investigation.",
                "choices": [goto("Talk to Salma and resume the journey", i + 1)],
            })
        if i in risky:
            choices.append({"text": "Challenge the smuggler with your sabre", "outcome": {
                "type": "fight", "foes": [foe], "onWin": i + 1}})
        scenes.append({"id": i, "title": title, "text": chapter + ". " + text, "choices": choices})
    scenes += [
        {"id": 64, "title": "Ending · The Scholars' Notebook",
         "text": "You join Salma and the scholars on new surveys. The residents retain copies of the maps. Your notebook carefully separates measurements from the stories you were told.", "choices": []},
        {"id": 65, "title": "Ending · Guardians of the Water",
         "text": "You stay with Amina to share the surveys and repair the crossings. Bonaparte continues his campaign; your adventure ends with work the villages can maintain for themselves.", "choices": []},
    ]
    places = [
        (0, "Scholars' Camp", "camp", -55, 55),
        (1, "Alexandria Harbour", "harbour", -55, 15),
        (2, "Nile Landing", "harbour", -15, 15),
        (3, "Reed Village", "village", 25, 50),
        (4, "Cairo Market", "market", 50, 5),
        (5, "Old Observatory", "ruins", 25, -35),
        (6, "Giza Plateau", "temple", -25, -55),
        (7, "Desert Outpost", "outpost", -65, -30),
    ]
    routes = [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,1),(2,5)]
    # Locations follow the activity, with regular trips inside each chapter.
    itinerary = [
        0,0,1,4,1,4,1,2,7,2,7,2,4,4,3,2,
        3,2,3,5,2,0,0,3,2,2,4,4,5,3,4,5,
        7,0,0,7,4,3,2,2,1,4,3,5,4,5,5,2,
        6,6,7,6,7,3,6,3,0,2,0,4,7,3,6,0,
        0,3,
    ]
    def place_for(scene):
        main = scene if scene < 100 else scene % 100
        return itinerary[main]
    environment = {
        "theme": "desert",
        "places": [dict(id=i, name=n, kind=k, x=x, z=z) for i,n,k,x,z in places],
        "paths": [dict(fromPlace=a, toPlace=b) for a,b in routes],
        "props": [dict(kind=k,x=x,z=z,scale=scale,heading=heading) for k,x,z,scale,heading in [
            ("pyramid", -58,-78,150,0), ("pyramid",-6,-91,180,0),
            ("pyramid",-86,-68,80,0), ("river",-6,20,120,0),
            ("boat",-7,44,100,0), ("palm",-32,48,100,0),
            ("palm",9,78,140,0), ("palm",68,41,130,0),
            ("palm",-33,1,120,0), ("rock",73,-54,150,30),
            ("rock",-83,74,150,40), ("house",75,70,150,0),
            ("column",48,-65,140,0), ("column",59,-65,140,0),
        ]],
        "scenes": [dict(scene=s["id"], place=place_for(s["id"]), npcs=[n for n in
                   ["Napoleon Bonaparte", "Salma", "Amina", "Youssef", "Farid", "Monge", "Desaix"]
                   if n in s["text"]][:4]) for s in scenes],
    }
    return {
        "environment": environment,
        "title": "Bonaparte · Maps of the Nile", "world": "Egypt, Bonaparte's expedition, 1798",
        "intro": "Egypt, July 1798. You are Camille Laurent, an interpreter and cartographer with the expedition. Alongside Salma, you search for stolen surveys that threaten access to water. This historical fiction takes you from Alexandria to the Nile, Cairo and the pyramids of Giza.",
        "fairnessProfile": "exploration-10-v1", "character": hero, "start": 0,
        "themeNames": {"skills": [{"skill": "broadsword", "name": "Sabre Fencing"}, {"skill": "stealth", "name": "Stealth"},
                                  {"skill": "diplomacy", "name": "Negotiation"}, {"skill": "lockpicking", "name": "Lockpicking"}],
                       "weapons": [{"weapon": "broadsword", "name": "Expedition Sabre"}],
                       "armor": [{"armor": "leather", "name": "Reinforced Coat"}]},
        "palette": ["#d9b878", "#b9894d", "#ead9ab", "#254c62", "#193747", "#6d4d35"],
        "scenes": sorted(scenes, key=lambda s: s["id"]),
        "wish": "A long adventure with Napoleon during the Egyptian campaign and the Battle of the Pyramids.",
        "fairnessSeed": 20261103,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--install', action='store_true', help='Check and install in the local adventure library')
    args = parser.parse_args()
    started = time.perf_counter()
    adventure = assemble()
    destination = ROOT / "campaigns" / "napoleon.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(adventure, ensure_ascii=False, indent=2) + "\n")
    metrics = {"file": str(destination), "scenes": len(adventure["scenes"]),
                      "shortest_successful_path": len(STAGES),
                      "assembly_ms": (time.perf_counter() - started) * 1000,
                      "source": "locally authored text, no generative API"}
    if args.install:
        result = subprocess.run([str(ROOT / '.lake/build/bin/inspect-adventure'), str(destination),
                                 '--horizon', '14', '--seed', str(adventure['fairnessSeed'])],
                                capture_output=True, text=True, check=True)
        report = json.loads(result.stdout)
        folder = ROOT / 'adventures/2-bonaparte-les-cartes-du-nil'
        folder.mkdir(parents=True, exist_ok=True)
        (folder / 'adventure.json').write_bytes(destination.read_bytes())
        metrics.update(validation=report, installed=str(folder),
                       total_ms=(time.perf_counter() - started) * 1000)
        (folder / 'creation-metrics.json').write_text(json.dumps(metrics, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(metrics, ensure_ascii=False))


if __name__ == "__main__":
    main()
