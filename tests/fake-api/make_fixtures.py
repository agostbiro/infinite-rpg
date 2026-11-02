#!/usr/bin/env python3
"""Write the recorded API replies in this folder, for the test hook RPG_FAKE_API.

Each reply is a stream of server-sent events (SSE), the form the API sends for a request with
"stream": true: message_start, then each content block (a thinking block with its signature, and
a text block) as content_block_start, deltas, and content_block_stop, then message_delta with
the stop reason, and message_stop. The text is sent in small parts, as the API does.

refusal.sse is a refused reply. change-1.sse to change-3.sse are the replies for one live change:
the DM first calls the request unsupported, then forgets the counter-rule, then sends a change that
passes. There is no recorded Wish now: a Wish in test mode fails with "no recorded reply". The
follow-up in docs/follow-ups.md adds one back (adventure-1.sse, adventure-2.sse, and so on), with
the world map replies map-1.sse and map-2.sse. Without a map reply, the Adventure has no map.
Usage: make_fixtures.py FOLDER [--tuning]
Other tests import `stream` from this file to write their own recorded replies.
"""
import json, copy, sys

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

def write(out, name, text):
    """Write the recorded reply `name`.sse into the folder `out`."""
    with open(f"{out}/{name}.sse", "w") as f:
        f.write(text)


def main(out, tuning):
    """Write the recorded replies of this folder into `out`."""
    write(out, "refusal", stream(None, stop="refusal"))

    # A live rule change for Mara. The first reply wrongly claims it is
    # unsupported, the second omits a counter-rule, and the third implements the grant.
    change = {
        "supported": True,
        "summary": "You catch a Stormglass Flamethrower, its enchanted sight guiding your aim.",
        "moment": "Wounded bandits rally through the smoke. Finish them or guard behind a Cinder Veil.",
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
    write(out, "change-1", stream(json.dumps(unsupported_change)))
    write(out, "change-2", stream(json.dumps(bad_change)))
    if tuning:
        change["rules"][0].update(trigger="againstFlame", hitBonus=4, damageBonus=6, armorBonus=2)
        change["rules"][0]["description"] = "Enemies facing your flame gain +4 to hit, +6 damage, and 2 armor."
    write(out, "change-3", stream(json.dumps(change)))


if __name__ == "__main__":
    main(sys.argv[1], "--tuning" in sys.argv[2:])
