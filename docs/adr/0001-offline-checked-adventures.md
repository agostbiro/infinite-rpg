# Adventures are Lean files, checked before play

The DM (Dungeon Master) is an AI agent that writes each Adventure as a Lean file before play. A checker with a soundness proof makes each bundled Adventure carry a theorem that it is legal, so the build fails on an illegal Adventure. No LLM (large language model) runs during play. The Engine plays the Adventure alone, so the DM has no way to cheat once play starts.

## Considered options

- **Live DM that issues commands during play, checked by the Engine.** Gives a more reactive game, but needs a command language, an LLM client in Lean, and a retry loop. Deferred.
- **Live generation of an Adventure as JSON (JavaScript Object Notation), checked at run time.** Lets the Player ask for any Adventure, but adds an HTTP client, a JSON format, an API key, and network failures during a demo. Deferred. It can be added later, because it produces the same `Adventure` type.
- **Lean code generated at run time.** Rejected. It needs the Lean toolchain at run time, and DM-written Lean can run code or add axioms while it is checked.

## Consequences

The Player cannot ask for a new Adventure at play time. The no-cheating demo is a cheating Adventure that fails the build, not a live rejection.
