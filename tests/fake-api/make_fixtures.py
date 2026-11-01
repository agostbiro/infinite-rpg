#!/usr/bin/env python3
"""Write the recorded API replies in this folder, for the test hook RPG_FAKE_API.

Each reply is a stream of server-sent events (SSE), the form the API sends for a request with
"stream": true: message_start, then each content block (a thinking block with its signature, and
a text block) as content_block_start, deltas, and content_block_stop, then message_delta with
the stop reason, and message_stop. The text is sent in small parts, as the API does.

adventure-1.sse fails the checker (4 errors). adventure-2.sse passes. picture.sse is a
Picture that passes scripts/check_pictures.py, and picture-4.sse one that fails it (a script).
refusal.sse is a refused reply. Usage: make_fixtures.py FOLDER
"""
import json, copy, sys
out = sys.argv[1]

pip = {"name": "Pip Tunnelly", "background": "A young hobbit of Bywater who reads the weather better than books, and talks his way out of most trouble.",
       "st": 8, "dx": 12, "iq": 11, "ht": 12,
       "skills": [{"skill": "stealth", "level": 14}, {"skill": "knife", "level": 14},
                  {"skill": "fastTalk", "level": 13}, {"skill": "naturalist", "level": 12},
                  {"skill": "survival", "level": 12}, {"skill": "climbing", "level": 13},
                  {"skill": "swimming", "level": 13}, {"skill": "firstAid", "level": 12}],
       "weapon": "largeKnife", "armor": "none"}
wolf = {"name": "Grey Wolf", "st": 9, "dx": 12, "iq": 4, "ht": 12, "skills": [{"skill": "brawling", "level": 12}],
        "weapon": "punch", "armor": "none", "naturalDR": 1}
ruffian = {"name": "Bree Ruffian", "st": 11, "dx": 10, "iq": 9, "ht": 11, "skills": [{"skill": "knife", "level": 11}],
           "weapon": "largeKnife", "armor": "leather", "naturalDR": 0}

def goto(n, text): return {"text": text, "outcome": {"type": "goto", "next": n}}
def roll(t, m, s, f, text): return {"text": text, "outcome": {"type": "roll", "against": t, "modifier": m, "onSuccess": s, "onFailure": f}}
def fight(foes, w, text): return {"text": text, "outcome": {"type": "fight", "foes": foes, "onWin": w}}

scenes = [
  {"id": 0, "title": "The Garden Gate", "text": "Morning mist lies over Bywater. Old Mother Burrows hammers on your gate: her grandson's silver acorn, an heirloom, was snatched in the night, and muddy boot prints lead off toward the river. The sky to the west looks heavy.",
   "choices": [goto(1, "Walk down the lane to the Green Dragon"), roll("naturalist", 0, 2, 1, "Read the clouds before you go (Weather-lore)")]},
  {"id": 1, "title": "The Green Dragon", "text": "The inn is warm and loud. In the corner a tall stranger in a wet cloak keeps his hand on a bulging pocket and watches the door.",
   "choices": [roll("fastTalk", -1, 3, 4, "Spin him a tale and look in his pocket (Hobbit Chatter -1)"), goto(4, "Follow him when he slips out")]},
  {"id": 2, "title": "Bagshot Hill", "text": "You climb the hill and see the storm coming. From up here you also see the path the thief took: across Farmer Cotton's fields, toward the ferry.",
   "choices": [goto(3, "Take the short way through the fields")]},
  {"id": 3, "title": "Farmer Cotton's Fields", "text": "Tall barley hides you. Ahead, by the hedge, something grey and lean is sniffing the thief's trail.",
   "choices": [roll("stealth", 0, 5, 4, "Creep past it through the barley (Hobbit Quietness)"), goto(4, "Walk up to it boldly")]},
  {"id": 4, "title": "Teeth in the Hedge", "text": "A grey wolf, far from the wild, bursts out of the hedge with a snarl.",
   "choices": [fight([wolf], 5, "Stand and fight")]},
  {"id": 5, "title": "The Brandywine Bank", "text": "The river runs fast and brown after the night's rain. On the far bank the stranger is loading a little boat.",
   "choices": [roll("swimming", -2, 6, 7, "Swim across before he casts off (Swimming -2)"), goto(7, "Run for the ferry")]},
  {"id": 6, "title": "Ending: Home by Supper", "text": "You haul yourself out of the water right beside the boat. The stranger is so startled that he drops the silver acorn and flees. You are back in Bywater in time for supper, and Mother Burrows bakes you a seed cake.",
   "choices": []},
  {"id": 7, "title": "The Ferry", "text": "At the ferry the stranger turns and draws a long knife. \"Go home, little one,\" he says.",
   "choices": [fight([ruffian], 8, "Fight the ruffian")]},
  {"id": 8, "title": "Ending: The Acorn Returned", "text": "The ruffian goes into the river and comes up far downstream, with no acorn and no pride. The Shirriffs hear the tale by evening, and your name is toasted at the Green Dragon for a week.",
   "choices": []},
]
good = {
  "title": "The Silver Acorn",
  "character": pip,
  "themeNames": {"skills": [{"skill": "stealth", "name": "Hobbit Quietness"}, {"skill": "fastTalk", "name": "Hobbit Chatter"},
                            {"skill": "naturalist", "name": "Weather-lore"}, {"skill": "knife", "name": "Blade-work"},
                            {"skill": "survival", "name": "Wild-lore"}],
                 "weapons": [{"weapon": "largeKnife", "name": "Grandfather's Barrow-blade"}],
                 "armor": [{"armor": "none", "name": "Second-best Waistcoat"}]},
  "palette": ["#1d2a1a", "#2f4a2a", "#4d6b3a", "#86a35a", "#c9b46a", "#e8d9a8", "#6b4a2a", "#3a2a1c", "#7a9ab8", "#2a3a52"],
  "start": 0,
  "scenes": scenes,
}
bad = copy.deepcopy(good)
bad["character"]["st"] = 9
bad["scenes"][7]["choices"][0]["outcome"]["onWin"] = 9

def event(kind, data):
    return f"event: {kind}\ndata: {json.dumps(data)}\n\n"

def chunks(text, n=200):
    return [text[i:i + n] for i in range(0, len(text), n)] or [""]

def stream(text, stop="end_turn"):
    """The SSE events of one reply with a thinking block and, if `text` is not None, a text block."""
    out = [event("message_start", {"type": "message_start", "message": {
        "id": "msg_fixture", "type": "message", "role": "assistant", "model": "claude-opus-5-5",
        "content": [], "stop_reason": None, "stop_sequence": None,
        "usage": {"input_tokens": 100, "output_tokens": 1}}})]
    if text is not None:
        out.append(event("content_block_start", {"type": "content_block_start", "index": 0,
            "content_block": {"type": "thinking", "thinking": "", "signature": ""}}))
        out.append(event("ping", {"type": "ping"}))
        for part in ["Plan the ", "Adventure."]:
            out.append(event("content_block_delta", {"type": "content_block_delta", "index": 0,
                "delta": {"type": "thinking_delta", "thinking": part}}))
        for part in ["fixture-sig-", "part-2"]:
            out.append(event("content_block_delta", {"type": "content_block_delta", "index": 0,
                "delta": {"type": "signature_delta", "signature": part}}))
        out.append(event("content_block_stop", {"type": "content_block_stop", "index": 0}))
        out.append(event("content_block_start", {"type": "content_block_start", "index": 1,
            "content_block": {"type": "text", "text": ""}}))
        for part in chunks(text):
            out.append(event("content_block_delta", {"type": "content_block_delta", "index": 1,
                "delta": {"type": "text_delta", "text": part}}))
        out.append(event("content_block_stop", {"type": "content_block_stop", "index": 1}))
    out.append(event("message_delta", {"type": "message_delta",
        "delta": {"stop_reason": stop, "stop_sequence": None}, "usage": {"output_tokens": 500}}))
    out.append(event("message_stop", {"type": "message_stop"}))
    return "".join(out)

def write(name, text):
    with open(f"{out}/{name}.sse", "w") as f:
        f.write(text)

write("adventure-1", stream(json.dumps(bad)))
write("adventure-2", stream(json.dumps(good)))
svg = ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1200 400" width="1200" height="400">'
       '<defs><linearGradient id="sky" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#2a3a52"/><stop offset="1" stop-color="#7a9ab8"/></linearGradient></defs>'
       '<rect width="1200" height="400" fill="url(#sky)"/>'
       '<circle cx="900" cy="110" r="46" fill="#e8d9a8"/>'
       '<path d="M0 300 Q300 200 600 280 T1200 260 V400 H0 Z" fill="#4d6b3a"/>'
       '<path d="M0 340 Q400 280 800 330 T1200 320 V400 H0 Z" fill="#2f4a2a"/>'
       '<circle cx="520" cy="300" r="34" fill="#c9b46a"/><rect x="505" y="300" width="30" height="40" fill="#6b4a2a"/>'
       '</svg>')
write("picture", stream(json.dumps({"svg": svg})))
write("picture-4", stream(json.dumps({"svg": svg.replace("</svg>", "<script>alert(1)</script></svg>")})))
write("refusal", stream(None, stop="refusal"))

# A live rule change for Mara at the Shore. The first reply wrongly claims it is
# unsupported, the second omits a counter-rule, and the third implements the grant.
change = {
    "supported": True,
    "summary": "You catch a Stormglass Flamethrower, its enchanted sight guiding your aim.",
    "moment": "Wounded wreckers rally through the smoke. Finish them or guard behind a Cinder Veil.",
    "equipment": {"weapon": "flamethrower", "name": "Stormglass Flamethrower",
                  "attackLevel": 12, "dice": 3, "add": 0},
    "requestedRules": [],
    "rules": [
        {"name": "Scorched Fury", "description": "Enemies at half HP or less gain +3 to hit and +2 damage. Finish them before they rally!",
         "side": "foes", "trigger": "wounded", "hitBonus": 3, "damageBonus": 2, "armorBonus": 0},
        {"name": "Cinder Veil", "description": "All-Out Defense wraps you in ash: +2 armor until your next maneuver.",
         "side": "hero", "trigger": "guarding", "hitBonus": 0, "damageBonus": 0, "armorBonus": 2},
    ],
    "scenes": [],
}
bad_change = copy.deepcopy(change)
bad_change["rules"] = []
unsupported_change = {
    "supported": False, "summary": "I cannot represent that equipment.",
    "moment": "", "equipment": None, "requestedRules": [], "rules": [], "scenes": [],
}
write("change-1", stream(json.dumps(unsupported_change)))
write("change-2", stream(json.dumps(bad_change)))
if "--tuning" in sys.argv[2:]:
    change["rules"][0].update(trigger="againstFlame", hitBonus=4, damageBonus=6, armorBonus=2)
    change["rules"][0]["description"] = "Enemies facing your flame gain +4 to hit, +6 damage, and 2 armor."
write("change-3", stream(json.dumps(change)))
