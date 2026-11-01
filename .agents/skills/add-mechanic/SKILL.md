---
name: add-mechanic
description: Add a game mechanic, described in plain words, to the RPG and keep every adventure admitted under the fairness theorem `StatisticalCandidate.fair`, adding a fun counter-mechanic when the first one breaks fairness. Use when the user describes a new rule, mechanic, or house rule for the game.
---

# Add a mechanic and keep the game fair

The user describes a **mechanic** in plain words. You build it, then keep every
adventure fair. If the mechanic breaks fairness, you add a second, fun
**counter-mechanic** that pulls the numbers back inside the bounds. The user's
mechanic stays in, at the strength the user asked for.

Read `Rpg/RuleSet.lean`, `Rpg/Engine.lean`, `Rpg/Probability/Combat.lean`,
`Rpg/Probability/StatisticalAdmission.lean`, and `docs/statistical-confidence.md`
before step 1.

## What "fair" means here

`Rpg.Probability.StatisticalCandidate.fair` proves `Fair a` once, for every
candidate. It says the admission test is sound: each confidence interval misses
the true death chance with probability at most 0.1%, and so does a false
"accept". The true death chances come from the **model** (`adventureGraph`).
The proof assumes the **simulation** that admission runs draws games with the
model's chances.

A mechanic can break three things:

- **Agreement.** If the mechanic reaches the simulation but not the model (or
  the reverse), admission can still pass, but `fair` is then about a different
  game. Nothing in the build catches this. Step 2 prevents it.
- **The build.** Each adventure's `fair` theorem (`Rpg.Harbor.fair`,
  `Rpg.Lighthouse.fair`) and its legality proofs must still compile.
- **Admission.** At start-up, `admitStatistically` plays many games with the
  fixed `validationSeed` and checks each row: death on turn 1, and death on turn
  `t+2` given alive at turn `t`, for `t` below the adventure's `horizon`. A row
  passes when its whole confidence interval (death frequency ±4 points) fits in
  the Weibull band. An adventure that fails is left out of the menu.

So the goal is: every adventure in `statisticalCandidates` (`Rpg/Catalog.lean`)
keeps play, simulation, and model in agreement, still builds, and still passes
admission.

## Fixed ground

The fairness bar is fixed. You move the game to meet it:

- `Rpg/Probability/Weibull.lean`, `Rpg/Probability/Confidence.lean`,
  `Rpg/Probability/StatisticalAdmission.lean`, `Rpg/Probability/Graph.lean`,
  `Rpg/Probability/Combat.lean`, and `Rpg/Spec.lean` keep their meaning. This
  includes the policy constants, the sample size, the error radius, the
  validation seed, the game limit, and the round limit.
- Each adventure's `fairnessHorizon` stays as it is (in
  `Rpg/Adventures/Harbor/Certification.lean` and
  `Rpg/Adventures/Lighthouse/Confidence.lean`).
- The constants in `screen.lean` and `agree.lean` stay as they are. You only add
  fights to `cases` in `agree.lean`.
- The catalog keeps every adventure it has. Stories, heroes, and creatures stay
  as they are; only mechanics change.
- The numbers you fix in step 1 for the user's mechanic stay as they are.
- Proofs use no `sorry`, `axiom`, `native_decide`, or `maxHeartbeats 0`.

If a step seems to need any of these, stop and ask the user.

## Steps

### 1. Pin the mechanic down

Rewrite the request as a rule with exact numbers: when it fires, what it
changes, and by how much. Then name the code it touches:

- **Rule mechanic**: changes how dice, damage, defense, or turn order work. It
  lives in `RuleSet`. Use an existing field if one fits. Otherwise add a field
  whose default is today's behaviour.
- **Content mechanic**: needs a new kind of thing in a story (for example a new
  `Outcome`). This changes `Rpg/Adventure.lean` and `Rpg/Spec.lean`, which are the
  trusted spec. Ask the user before you edit them.

**Memory.** The model knows only each fighter's HP and the current scene. A
mechanic that must remember something ("once per fight", a cooldown, a potion
count) has nowhere to keep it. Rephrase it as a condition on current HP or on
the dice: "once per fight, when you first fall below 1/3 HP" becomes "while you
are below 1/3 HP". If the user's mechanic loses its point that way, ask the
user. Real memory needs new fields in `FightState` and `Node` and a new
termination measure in `solveCombat`, which are fixed ground.

Target adventures: the ones the user names, else every adventure in
`statisticalCandidates`.

Done when you can state the rule in one sentence with numbers, it needs no
memory, and if two readings of the request would give different fairness
results, the user has picked one.

### 2. Build it in the shared code

Play (`Main.lean`), simulation (`Estimate.trajectory`), and model
(`adventureGraph`) share only some functions. Put the mechanic only there:

- **Fights**: `attackWith`, `takeTurnWith`, `turnOrder`, and the helpers they
  call (`Fighter.dodge`, `hurtFoe`, `FightState.over`), or a `RuleSet` field
  that these read. Play and simulation reach them through `fightRound`; the
  model reaches them through `roundDistribution` in `Combat.lean`. Code in
  `fightRound`, `takeTurn`, `attack`, or `Estimate.fight` reaches play and
  simulation only.
- **Scene rolls**: the `successRoll` field and `Being.rollLevel`. Play and
  simulation use `makeRoll`; the model uses `rollProbability`. Both read these.
- **Between scenes** (HP changes after a scene): there is no shared function.
  This needs edits to `Graph.lean`, which is fixed ground. Ask the user.

Turn the mechanic on in each target adventure's `Rules.lean` by adding the field
to the existing value, for example `{ halveDodgeBelowThird := false, myMechanic := true }`.

Traps:

- `solveCombat` treats any fight round that changes the state but does not
  lower total living HP as `stalled`: a game that never ends. Healing inside a
  fight does this. Mechanics may only lower HP or leave the state unchanged.
- A fight that lasts more than `validationRoundLimit` (200) rounds inside the
  window aborts admission. Mechanics that add defense make fights longer.
- Each row needs 160,000 games that are still alive at its turn, within two
  million games. A mechanic that ends games early can leave the late rows
  unfilled, and then the adventure fails.
- The new field's default must keep old behaviour exactly.

Add tests next to the code:

- The mechanic fires when on, and nothing changes when off (`#guard` or `example`).
- **Agreement**: run [`agree.lean`](agree.lean) with the mechanic on
  (`lake env lean .agents/skills/add-mechanic/agree.lean`). It compares the
  model's death chance for a fight with the frequency over 20,000 simulated
  fights. Add one fight from each target story to `cases`. Every line must
  say `ok` (gap under 1 point).

Write a line to the play log when the mechanic fires, so the player sees it.

Done when `lake build` passes and all tests pass.

### 3. Screen fairness

Run [`screen.lean`](screen.lean) from the repo root:

```
lake env lean .agents/skills/add-mechanic/screen.lean
```

It plays every adventure in `statisticalCandidates` the same way admission does,
with its own seed, 20,000 observations per row, and the same games-per-row
limit, in about 20 seconds. Each row shows the death frequency, the range
admission accepts, and `ok`, `FAIL`, or `NOT FILLED`. `ABORTED` means a fight hit
the round limit or a game was invalid.

Run it with the mechanic off and with it on. Keep both outputs for the report.

Done when you have before and after numbers for every target. If every row is
`ok` with at least 2 points of margin, go to step 5. Otherwise go to step 4.

### 4. Counterbalance with a fun mechanic

Design one counter-mechanic that pushes the failing rows back inside their
range. It is its own `RuleSet` field, separate from the user's mechanic. It is a
real mechanic, not a number tweak to the hero or a creature. It follows the
step 1 and step 2 rules: no memory, shared code only. It is fun:

- The player feels it: a dramatic moment, a comeback, a choice, or a log line
  worth reading.
- It fits the theme of the user's mechanic (deadlier critical hits pair well
  with a "last stand" dodge bonus below 1/3 HP; a cursed weapon pairs with a
  lucky parry on a defense roll of 4 or less).
- The user's mechanic keeps its step 1 numbers and its step 2 test.

Build it with step 2's rules, then screen again with step 3. Adjust its numbers,
or try a different counter-mechanic, until every row is `ok` with at least 2
points of margin. The screen has about ±1 point of noise; the margin covers it.

Done when the screen passes for every target. If three different
counter-mechanics fail, stop and report the numbers to the user.

### 5. Freeze, then admit once

Tune only with the screen. The validation seed is a held-out test: it counts
only if you look at it after the mechanics are final. Freeze the mechanics, then
run:

```
make check
make run < /dev/null
```

`make check` builds and replays every proof in the kernel; it fails on `sorry`
and on new axioms. `make run < /dev/null` runs admission for every adventure
(about 10 seconds), prints `passed` or `not admitted` for each, then exits.

If an adventure is not admitted, stop and report to the user with the screen
numbers. Changes tuned after a failed validation need a fresh held-out seed,
and that choice is the user's.

As a second axiom check, write a scratch file outside the repo with
`import Rpg.Catalog` and one `#print axioms Rpg.<Adventure>.fair` line per
target, and run it with `lake env lean <file>`. Only `propext`,
`Classical.choice`, and `Quot.sound` may appear.

Done when `make check` passes, every target prints `passed`, and the axioms are
clean.

### 6. Document

- Add an entry per new mechanic to `docs/gurps-deviations.md`, in its existing
  format. Add new terms to `GLOSSARY.md`.
- If Lighthouse's counts changed, update them from `make validate` in two
  places: the table in `docs/statistical-confidence.md`, and
  `recordedValidation` in `Rpg/Adventures/Lighthouse/ValidationExample.lean`.
  The build does not catch stale counts there.

## Report

Tell the user, briefly:

- The mechanic as built, in one sentence with numbers.
- The counter-mechanic, if any, and why it was needed.
- Before and after screen numbers per target, for the rows that moved.
- The agreement test results.
- The admission result per adventure, and the axiom list.
- Anything you had to ask about or could not do.
