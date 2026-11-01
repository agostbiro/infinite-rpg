---
status: accepted
---

# Live Adventures, checked at run time

This replaces ADR 0001. The Player types a Wish in the GUI (graphical user interface), and the server asks an LLM (large language model) for an Adventure and a Character as JSON. The server plays them only if the proved checker finds no errors. `Game.new` takes `{a // LegalAdventure c a}` and a proof of `LegalCharacter c` (since ADR 0004 it takes an `AdventureDefinition`, which holds both proofs, and a Wish must also pass the balance check), and the server can build these only from `check_sound` and `checkCharacter_sound`, so no unchecked Adventure can be played. The DM still works only before play, so it still has no way to change a roll.

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
- The Front Page shows whether each saved Adventure passes. That check runs the balance check, so it takes a second or two for each save. The server keeps the result in `adventures/<id>/verdict.json`, with a stamp of the checked `adventure.json` and a build key (the size and a hash of the server program file), and uses it again only if both match. Every new build of the server makes all verdicts old, because the checker, the rules, the balance check, the simulator, and the Draft reader are compiled into it. In the `lean` interpreter, verdicts are off. A load trusts a verdict that passed: if the verdict (or the cache) says that this build passed this exact text, the load runs only the checker again, which takes milliseconds, and skips the balance check. Without such a verdict, the load runs the checker and the balance check. A changed file or a new build makes the verdict old, so the full check runs again. So the verdict file is trusted for the balance check only: a person who edits or forges `verdict.json` could get a legal Adventure played that did not pass the balance check. Anyone who can write that file can also replace the server program. A wrong "fails" verdict is fixed by "Check again" on its card, which runs both checks.
