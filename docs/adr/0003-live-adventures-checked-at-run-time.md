---
status: accepted
---

# Live Adventures, checked at run time

This replaces ADR 0001. The Player types a Wish in the GUI (graphical user interface), and the server asks an LLM (large language model) for an Adventure and a Character as JSON. The server plays them only if the proved checker finds no errors. `Game.new` takes `{a // LegalAdventure c a}` and a proof of `LegalCharacter c` (since ADR 0004 it takes an `AdventureDefinition`, which holds both proofs, and a Wish must also pass the fairness check), and the server can build these only from `check_sound` and `checkCharacter_sound`, so no unchecked Adventure can be played. The DM still works only before play, so it still has no way to change a roll. (Since ADR 0005, the DM can propose a checked rule change during play. It still never picks a die face.)

## Considered options

- **Keep offline Adventures only (ADR 0001).** Nothing new to trust, but a Player cannot ask for "Hogwarts" without a coding agent. Rejected: it is the demo.
- **Generate Lean code at run time.** Rejected, as in ADR 0001: it needs the Lean toolchain at run time, and DM-written Lean can run code or add axioms while it is checked.
- **An HTTP client in Lean.** Core `Std.Http` has no TLS (Transport Layer Security), and the Claude API accepts only HTTPS. The server calls `curl` through `IO.Process`. The call has no proofs, and needs none: the checker runs on whatever comes back.

## Consequences

- A new trusted point: the compiled `check` must give the same answer as the `check` in the proof. Shipped Adventures still have a kernel-checked theorem.
- `make run` works without an API key, but then only the built-in Adventure can be played.
- If the check fails, the server sends the errors back to the LLM, up to 3 tries. The page shows each try and each error.
- Pictures for live Adventures are checked at run time by `scripts/check_pictures.py`. A Picture that fails becomes the plain backdrop.
- Adventures that pass are saved under `adventures/` and checked again on load, so a demo can run without the network.
