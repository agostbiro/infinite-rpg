#!/usr/bin/env python3
"""Generate local SSE fixtures, never presented as live Claude responses.
First reply has disconnected locations; the second contains a complete world.
The real decoder, checker and difficulty-specific admission run on every reply.
"""
import json, copy, sys
out = sys.argv[1]

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

from pathlib import Path
campaign = json.loads((Path(__file__).resolve().parents[2] / "campaigns/napoleon.json").read_text())
for field in ["wish", "fairnessSeed", "fairnessProfile"]:
    campaign.pop(field, None)
invalid = copy.deepcopy(campaign)
invalid["environment"]["paths"] = []
write("adventure-1", stream(json.dumps(invalid)))
write("adventure-2", stream(json.dumps(campaign)))
write("adventure-3", stream(json.dumps(campaign)))

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
