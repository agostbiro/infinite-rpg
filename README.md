# Verified RPG

A single-player text RPG (role-playing game) based on GURPS Lite. Adventures own
all their characters and selected rules. **The Drowned Lighthouse** and
**A Safe Harbor** become playable after their finite confidence intervals pass
the shared Weibull policy. The main theorem is called `fair`: Lean proves interval
coverage and the finite decision's false-acceptance bound under the accepted
IID/binomial sampling model.

```
make install
make run          # validates both adventures, then opens the game menu
make cheats       # watch the checker catch a cheating DM
make run SEED=7   # replay a game with the same dice
make validate     # frozen statistical protocol, about 12 seconds on the development machine
make audit        # fast exploratory diagnostics; not admission evidence
make check        # build, then replay every proof through the Lean kernel
```

## How it works

- The DM writes an Adventure as a Lean file, before play. See `docs/dm-prompt.md`.
- `Rpg/Spec.lean` says what a legal Adventure is, in plain Lean.
- `Rpg/Check.lean` has a checker that lists errors in plain words, and the theorem `check_sound`: if the checker finds no errors, the Adventure is legal by the spec.
- Every playable adventure carries character and story legality proofs, the
  finite `fair` theorem, and source-bound observations that passed admission.
  `StatisticalAdventure.intervals_fit` proves that every admitted interval fits
  its Weibull target's tolerance band.
- `Rpg/Probability/Confidence.lean` proves the variance bound, interval coverage,
  and false-acceptance bound. `StatisticalCandidate.fair` combines them for the
  adventure's finite window: `t < 6` for Lighthouse and `t < 1` for Harbor,
  together with a first-turn death check. Each interval has 99.9% coverage;
  accepting the entire window when any tested constraint is false has risk at
  most 0.1%. This is not simultaneous coverage of every interval.
- `Rpg/Probability/Weibull.lean` defines editable shared defaults: retention
  `4/5`, integer shape `1`, and absolute tolerance `1/5` (20 percentage points).
  These were deliberately relaxed after exploration, then frozen before a new
  validation seed was used. They are not universal RPG standards.
- `Rpg/Probability/Fairness.lean` defines expected termination time, expected death
  time, and death time conditional on eventual death. Infinite expectations and
  undefined conditioning events are distinguished.
- Each adventure owns `Rules.lean`, `Characters.lean`, and `Story.lean` in its
  own folder. Its graph and runtime use the same rules and hero, with HP retained
  after combat and uniform choices during analysis. Both character and story
  legality proofs are required.
  See [the probability model](docs/probability-model.md) for the exact criterion,
  assumptions, proof boundaries, and computation limits.
- The Engine (`Rpg/Engine.lean`) rolls all dice during play. No AI runs during play, so the DM has no way to change a roll.
- The Adventure types have no way to say "the Character loses HP". Harm only comes from Fights, which the Engine runs.
- `make check` runs `lake check`, which replays every proof through the Lean kernel. It fails if any proof uses `sorry` or a new axiom. The library builds every file under `Rpg/`, so a new Adventure is checked even if the game does not load it.

## What the spec checks

1. Every Creature satisfies its adventure’s attribute and point limits, has skills bought correctly, and enough ST for its weapon.
2. Every Success Roll modifier is within that adventure’s bounds.
3. Every Scene a Choice leads to exists, and so does the start Scene. No two Scenes share a number.
4. At least one Scene is an Ending.
5. Every Fight has a Creature and can end: the Character can hurt each Creature, or the Creature can hurt the Character. "Can hurt" checks possible attack, defense, and damage rolls under the selected rules. This is not a proof of almost-sure termination.
6. Every Scene can be reached from the start Scene.

Structural legality alone does not imply fairness or winnability. The separate
probabilistic policy constrains first-turn death and two-turn conditional death
probabilities. It does not guarantee victory or fairness under every strategy.

`Rpg/Adventures/Illegal.lean` has six cheating Adventures. For each, a proof shows the spec rejects it and the checker reports it.

## What is trusted

- The spec (`Rpg/Spec.lean`) and the definitions it uses in `Rpg/Rules.lean` and `Rpg/Adventure.lean`. Read these to know what the theorems mean.
- The rules in `Rpg/Rules.lean` were typed in from GURPS Lite by hand. A person must check them against the book.
- The probability definitions, graph builder, and combat elimination algorithm
  are trusted definitions. A general proof connecting combat elimination to
  infinite operational execution remains outstanding.
- The confidence theorem assumes the stated IID/binomial sampling model. It
  does not prove that SplitMix64 or the game implementation induces that law.
  These sampling assumptions are accepted; `fair` has no additional
  graph-normalization, active-start, or tail premises.
- The Engine and terminal have no overall correctness proof. Shared combat code
  was regression-checked against the previous engine on 1,024 seeded rounds.
- `lake check` requires Linux namespaces. On macOS, `lake build` checks declarations,
  but the additional isolated replay cannot run.
- Axioms: the theorems use only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Scope of this version (v0)

This is a 1-hour slice of the design. Left out for now: Items and Flags, Quick Contests, Parry, All-Out maneuvers, attack modes (each weapon has one), shock, rest, and more than one Character. Proofs about the Engine are also left for later.

Deviations from GURPS Lite are in `docs/gurps-deviations.md`. Design rules that are not GURPS rules: the point caps, the -10 to +10 modifier limit, and natural DR for Creatures at 5 points per level (the full GURPS price; GURPS Lite has no such trait). In turn order, a tie that is left after Basic Speed and DX goes to the Character; GURPS rolls for it.

Design notes: `GLOSSARY.md`, `docs/adr/`.
