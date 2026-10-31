# Verified RPG

A single-player text RPG (role-playing game) based on GURPS Lite. An AI DM (Dungeon Master) writes the adventures, and Lean checks each one against the game rules before anyone can play it. If the DM cheats, `make check` fails.

```
make install
make run          # play
make cheats       # watch the checker catch a cheating DM
make run SEED=7   # replay a game with the same dice
make check        # build, then replay every proof through the Lean kernel
```

## How it works

- The DM writes an Adventure as a Lean file, before play. See `docs/dm-prompt.md`.
- `Rpg/Spec.lean` says what a legal Adventure is, in plain Lean.
- `Rpg/Check.lean` has a checker that lists errors in plain words, and the theorem `check_sound`: if the checker finds no errors, the Adventure is legal by the spec.
- Each shipped Adventure has a theorem that it is legal, for example `lighthouse_legal`. The Lean kernel runs the checker to prove it.
- The Engine (`Rpg/Engine.lean`) rolls all dice during play. No AI runs during play, so the DM has no way to change a roll.
- The Adventure types have no way to say "the Character loses HP". Harm only comes from Fights, which the Engine runs.
- `make check` runs `lake check`, which replays every proof through the Lean kernel. It fails if any proof uses `sorry` or a new axiom. The library builds every file under `Rpg/`, so a new Adventure is checked even if the game does not load it.

## What the spec checks

1. Every Creature is a legal build: attributes 1 to 20, at most 150 points, skills bought correctly, ST high enough for its weapon.
2. Every Success Roll has a modifier from -10 to +10.
3. Every Scene a Choice leads to exists, and so does the start Scene. No two Scenes share a number.
4. At least one Scene is an Ending.
5. Every Fight has a Creature and can end: the Character can hurt each Creature, or the Creature can hurt the Character. "Can hurt" means an attack skill of 3 or more and a best hit that gets past DR.
6. Every Scene can be reached from the start Scene.

The spec does not say that an Adventure is fair or can be won. A Fight that the Character cannot win, or a Fight against many Creatures, is legal. Fairness rules are planned for a later version.

`Rpg/Adventures/Illegal.lean` has six cheating Adventures. For each, a proof shows the spec rejects it and the checker reports it.

## What is trusted

- The spec (`Rpg/Spec.lean`) and the definitions it uses in `Rpg/Rules.lean` and `Rpg/Adventure.lean`. Read these to know what the theorems mean.
- The rules in `Rpg/Rules.lean` were typed in from GURPS Lite by hand. A person must check them against the book.
- The Engine and the terminal code have no proofs yet.
- Axioms: the theorems use only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Scope of this version (v0)

This is a 1-hour slice of the design. Left out for now: Items and Flags, Quick Contests, Parry, All-Out maneuvers, attack modes (each weapon has one), shock, rest, and more than one Character. Proofs about the Engine are also left for later.

Deviations from GURPS Lite are in `docs/gurps-deviations.md`. Design rules that are not GURPS rules: the point caps, the -10 to +10 modifier limit, and natural DR for Creatures at 5 points per level (the full GURPS price; GURPS Lite has no such trait). In turn order, a tie that is left after Basic Speed and DX goes to the Character; GURPS rolls for it.

Design notes: `GLOSSARY.md`, `docs/adr/`.
