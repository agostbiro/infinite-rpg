---
name: add-mechanic
description: Add a game mechanic, described in plain words, to the RPG and keep every adventure admitted under the fairness theorem `StatisticalCandidate.fair`, adding a fun counter-mechanic when the first one breaks fairness. Use when the user describes a new rule, mechanic, or house rule for the game.
---

# Add a mechanic and keep the game fair

Implement the requested rule at its requested strength. Keep every registered
adventure legal and admitted under `StatisticalCandidate.fair`. If balancing is
needed, propose and implement a fun counter-rule that preserves the original
mechanic's appeal.

Read `Rpg/RuleSet.lean`, `Rpg/Engine.lean`, `Rpg/Probability/SharedRules.lean`,
`Rpg/Probability/StatisticalAdmission.lean`, and `docs/statistical-confidence.md`.

## Preserve the specification

Keep the shared Weibull policy, confidence level, game count, combat round limit,
validation seed, adventure horizons (and `liveHorizon` for Wishes in `Rpg/Live.lean`),
the model's Player (`heroPolicy` in `Combat.lean`, the same as `pickManeuver` in
`Simulation.lean`), catalog, and theorem statements fixed unless
the user has authorized a change. Existing authorization is sufficient; do not
ask again. A rule request may authorize changing its hero or story (for example,
giving Mara a weapon); make only that content change and keep it legal.

The main theorem proves per-row interval coverage and bounds false admission of
the finite Weibull checks under the accepted conditional-binomial sampling model.
It is not simultaneous interval coverage or a proof that the PRNG is IID.
Do not replace the proof, reduce the number of runs, widen a band, remove a late
row, discard timeouts, or search for a seed to make a mechanic pass.

## Shared parameters

Use the Lean definitions directly, not copied numeric defaults or helper-specific
run limits:

| Definition | Source | Use |
|---|---|---|
| `validationGames` | `StatisticalAdmission.lean` | Total games per adventure; simulated fights per optional agreement case |
| `validationRoundLimit` | `StatisticalAdmission.lean` | Maximum simulated rounds per fight |
| `confidenceDelta` | `Confidence.lean` | Binomial interval failure bound |
| `intervalSteps` | `Confidence.lean` | Endpoint precision through `confidenceInterval` |
| `defaultPolicy` | `Weibull.lean` | Targets and tolerance through `confidenceBands` |
| Candidate `horizon` | Adventure certification | Conditional death rows to test |

Screening uses the fixed `screenSeed` and `sampleCounts`. Final admission uses
`validationSeed` and `admitStatistically`, including source-bound evidence. Late
rows use their actual qualifying counts; zero observations fail.

## Build the rule in shared code

State the trigger, effect, and numbers before editing. Decide unspecified details
that fit the user's idea; do not silently change a once-per-fight rule into a
repeating rule to avoid tracking state.

- Put combat mechanics in `attackWith`, `heroTurnWith`, `foeTurnWith`,
  `foeTurnsWith`, `roundWith`, their shared helpers (`sprayWith`, `Fighter.dodge`,
  `hurtFoe`, `FightState.over`), or adventure `RuleSet` fields they read. These
  reach play (`Rpg/Play.lean`), simulation, and model.
- Put scene-roll mechanics in `RuleSet.successRoll` or `RuleSet.rollLevel`.
- Keep `attack`, `heroTurn`, `foeTurns`, `Game.characterTurn`, `roundDistribution`,
  and `Simulation.fight` routing through the shared functions.
  `Rpg/Probability/SharedRules.lean` checks these contracts for every input, and a
  `#guard` in `SimulationTests.lean` checks that play and the simulator end a Fight
  with the same HP from the same seed. Do not weaken them to permit a one-sided rule.
- The exact combat solver (`solveCombat`) solves the states with the same total HP
  together, and assumes such a group has few states (it searches at most 16) and
  that HP never goes up in a Fight.
- Keep HP between fights. New persistent state, healing inside combat, new scene
  outcomes, or graph changes require corresponding model/specification work;
  they are not covered by the routine fast path. Use existing authorization or
  ask for the missing scope before making such changes.
- Select a new configurable mechanic in the target adventures' `Rules.lean`.
  Its default preserves existing behavior for other adventures. People own the
  rules: `make check-rules` fails on a `Rules.lean` that is not `{}`, and
  `lighthouse_default_rules` in `Comparator/Statements.lean` states that the
  Lighthouse uses `{}`. A rule request authorizes this change: add the path to
  `RULES_ALLOW` in the Makefile, change that statement and its proof in
  `Comparator/Proofs.lean` to the new value, and say so in the report.
- Add small deterministic tests under `Rpg/` showing the trigger, effect, and
  disabled behavior. Test the new rule itself, not just that admission passes.
  Retain negative fixtures and adapt their data when the new rule changes them.
- Write a short play-log line when the mechanic fires.

The routing contracts check shared implementation structure. They do not prove
full stochastic model equivalence; the accepted sampling assumptions still apply.

## Make counter-rules fun

When a screen fails, identify which risk moved and why. Sketch two distinct,
named counter-rule ideas, then choose the one that adds the best player moment
while moving that risk in the needed direction. Do this without waiting for a
choice unless the user requested one.

For the chosen proposal, state:

- **The moment:** what surprising or dramatic thing the player sees happen.
- **The decision or payoff:** a new tactical choice, comeback opportunity, or
  satisfying risk/reward tradeoff; explain why it is fun in this adventure.
- **The rule:** an exact trigger and effect, with numbers and a sample log line.
- **The balance:** which failing rows it should improve and why the original
  requested mechanic remains powerful and recognizable.

Prefer a thematic behavior over a hidden numerical penalty. For example, stronger
criticals can pair with **Last Stand**, a visible low-HP defensive burst. A powerful
spray attack can provoke **Scorched Fury**: badly wounded enemies strike twice,
creating a reason to finish a dangerous target first. These are ideas, not required
mechanics; use the actual game's constraints and direction of imbalance.

Avoid canceling the new rule with an equal opposite modifier, tedious bookkeeping,
or arbitrary nerfs presented as exciting mechanics. Give the counter-rule its own
configuration and tests. Show the original rule working alongside it. Fairness
checks establish the statistical constraint; a short play-through checks whether
the moment is understandable and feels rewarding.

Tune only on exploratory screens. A small margin inside nontrivial policy bounds
is useful; it is a design buffer, not another confidence theorem. If several
reasonable ideas fail, report the tradeoff rather than weaken the specification.

## One-minute verification

From the repository root, run:

```sh
python3 .agents/skills/add-mechanic/scripts/check.py
```

The runner gives the entire verification one shared 60-second deadline. It builds
all `Rpg` proofs and regression modules plus compiled game/helper targets, checks
the axioms of every project theorem, and runs the compiled exploratory screen for
every catalog adventure. A failed check or timeout returns a nonzero status;
timeouts terminate child processes and report `INCOMPLETE`. Changed source inputs
also invalidate the result. Do not run another Lake process in this checkout at
the same time.

Record a baseline before the rule and compare it with the finished rule. Each
verification has its own deadline. The budget concerns checking a completed
candidate, not design, implementation, dependency installation, or every tuning
iteration combined. Large changes or a cold build can exceed it; never call an
unfinished check a pass or reduce the shared sampling parameters to meet it.

Runtime checks use compiled executables, never `#eval` or `lean --run`. The
runner's `lake env lean` call only audits proof metadata. Small build-time
regression checks remain allowed; do not add full held-out simulations to builds.

## Freeze, then validate once

Once the mechanics are final, run:

```sh
python3 .agents/skills/add-mechanic/scripts/check.py --final
```

Within the same deadline this also runs compiled, source-bound admission for all
adventures. On Linux it additionally requests `lake check`. On macOS it explicitly
reports isolated replay as pending; do not claim Comparator/replay passed. Final
proof replay requirements in `CLAUDE.md` still apply: run `make comparator` too.

If held-out validation fails, report it. Do not tune against that result and rerun
until success; changed mechanics then need an independently precommitted holdout.
Replaying an unchanged seed is reproducibility, not new independent evidence.

The old full-fight diagnostic remains available as `lake exe agree`. It uses
`validationGames`, `validationRoundLimit`, and `confidenceDelta`, but also exactly
enumerates all combat outcomes, which can exceed a minute. It is a separate deep
check, not part of the routine deadline or a proof of model equivalence. If work
changes model/sampler correspondence, additional checks or proofs are necessary;
do not describe the routine routing contracts as a substitute for that work.

## Report and document

Explain the new rule, the chosen counter-rule and why it is cool, the visible
player moment, and the before/after rows that moved. Report elapsed verification
time, admission status, and any incomplete deep checks or proof replay. Do not
claim fun has been mathematically proved.

Document new mechanics in `docs/gurps-deviations.md` and new terms in `GLOSSARY.md`.
After final validation, update the historical result table in
`docs/statistical-confidence.md` if it changed. Use the final command's output;
do not rerun the held-out batch merely to copy its numbers.
