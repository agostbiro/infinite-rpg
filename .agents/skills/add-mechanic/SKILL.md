---
name: add-mechanic
description: Add a game mechanic, described in plain words, to the RPG and keep every adventure admitted under the fairness theorem `StatisticalCandidate.fair`, adding a fun counter-mechanic when the first one breaks fairness. Use when the user describes a new rule, mechanic, or house rule for the game.
---

# Add a mechanic and keep the game fair

The user describes a **mechanic** in plain words. You build it, then keep every
adventure fair. If the mechanic breaks fairness, you add a second, fun
**counter-mechanic** that pulls the numbers back inside the bounds. The user's
mechanic stays in, at the strength the user asked for.

You decide every open detail of the mechanic yourself: pick the **most fun**
option, meaning the one the player feels most in play (bigger moments, more
visible log lines), within the rules. List each choice in the report.

Read `Rpg/RuleSet.lean`, `Rpg/Engine.lean`, `Rpg/Probability/Combat.lean`,
`Rpg/Probability/StatisticalAdmission.lean`, and `docs/statistical-confidence.md`
before step 1.

## What "fair" means here

`Rpg.Probability.StatisticalCandidate.fair` proves `Fair a` once, for every
candidate. It says the admission test is sound: each confidence interval misses
the true death chance with probability at most 10%, and so does a false
"accept". The true death chances come from the **model** (`adventureGraph`).
The proof assumes the **simulation** that admission runs draws games with the
model's chances.

A mechanic can break three things:

- **Agreement.** If the mechanic reaches the simulation but not the model (or
  the reverse), admission can still pass, but `fair` is then about a different
  game. Nothing in the build catches this. Step 2 prevents it.
- **The build.** Each adventure's `fair` theorem (`Rpg.Lighthouse.fair`) and its
  legality proofs must still compile. `ValidationExample.lean` records the
  Lighthouse counts; if the mechanic changes them, record the new counts and say why.
- **Admission.** At start-up, `admitStatistically` plays many games with the
  fixed `validationSeed` and checks each row: death on turn 1, and death on turn
  `t+2` given alive at turn `t`, for `t` below the adventure's `horizon`. A row
  passes when its whole 90% exact binomial interval enclosure fits in
  the Weibull band. If the Lighthouse fails, the server does not start. Wishes
  run the same check with a fresh seed, so a mechanic also changes which Wishes pass.

So the goal is: every adventure in `statisticalCandidates` (`Rpg/Catalog.lean`)
keeps play, simulation, and model in agreement, still builds, and still passes
admission.

## Fixed ground

The fairness bar is fixed. You move the game to meet it:

- `Rpg/Probability/Weibull.lean`, `Rpg/Probability/Binomial.lean`,
  `Rpg/Probability/Confidence.lean`,
  `Rpg/Probability/StatisticalAdmission.lean`, `Rpg/Probability/Graph.lean`,
  `Rpg/Probability/Combat.lean`, and `Rpg/Spec.lean` keep their meaning. This
  includes the policy constants, confidence level, interval precision,
  validation seed, fixed game count, and round limit.
- Each adventure's `fairnessHorizon` stays as it is (in
  `Rpg/Adventures/Lighthouse/Confidence.lean`), and so does `liveHorizon` in `Rpg/Live.lean`.
- The model's Player (`heroPolicy` in `Combat.lean`) and the simulator's Player
  (`pickManeuver` in `Simulation.lean`) stay the same as each other.
- The constants in `screen.lean` and `agree.lean` stay as they are. You only add
  fights to `cases` in `agree.lean`.
- The catalog keeps every adventure it has. Stories, heroes, and creatures stay
  as they are; only mechanics change. The exception is a mechanic that is itself
  a change to them ("give the hero a flamethrower"): make only that change, and
  keep the hero legal.
- The numbers you fix in step 1 for the user's mechanic stay as they are.
- Proofs use no `sorry`, `axiom`, `native_decide`, or `maxHeartbeats 0`.

If a step seems to need any of these, stop and ask the user. These are the only
questions you ask.

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
are below 1/3 HP". Pick the most fun version that needs no memory. Real memory
needs new fields in `FightState` and `Node` and a new
termination measure in `solveCombat`, which are fixed ground.

Target adventures: the ones the user names, else every adventure in
`statisticalCandidates`.

**Open choices.** The request often leaves details open: the numbers, which
foes it hits, how the hero pays the points for it. Decide each one: pick the
most fun option.

Done when you can state the rule in one sentence with numbers, it needs no
memory, and every open choice is decided.

### 2. Build it in the shared code

Play (`Play.lean`), simulation (`Simulation.trajectory`), and model
(`adventureGraph`) share only some functions. Put the mechanic only there:

- **Fights**: `attackWith`, `heroTurnWith`, `foeTurnWith`, `foeTurnsWith`,
  `turnOrder`, and the helpers they call (`Fighter.dodge`, `hurtFoe`,
  `FightState.over`, `sprayWith`), or a `RuleSet` field that these read.
  Play (`Play.lean`) reaches them through `heroTurn` and `foeTurns`; the simulation
  through `roundWith`; the model through `roundDistribution` in `Combat.lean`.
  Code in `roundWith`, `heroTurn`, `foeTurns`, `attack`, `Game.characterTurn`, or
  `Simulation.fight` reaches play or simulation only.
- **Scene rolls**: the `successRoll` field and `RuleSet.rollLevel`. Play and
  simulation use `makeRoll`; the model uses `rollProbability`. Both read these.
- **Between scenes** (HP changes after a scene): there is no shared function.
  This needs edits to `Graph.lean`, which is fixed ground. Ask the user.

Turn the mechanic on in each target adventure's `Rules.lean` by adding the field
to the existing value, for example `{ halveDodgeBelowThird := false, myMechanic := true }`.
People own the rules: `make check-rules` fails on a `Rules.lean` that is not `{}`. Add
its path to `RULES_ALLOW` in the Makefile, and say so in the report, so the user approves it.

Traps:

- `solveCombat` solves the states with the same total living HP together, and
  assumes that a group has few states (it searches at most 16) and that HP never
  goes up. Healing inside a fight breaks this. Mechanics may only lower HP, or change
  the state in a way that keeps the groups small (as the maneuver does).
- A fight that lasts more than `validationRoundLimit` (200) rounds inside the
  window aborts admission. Mechanics that add defense make fights longer.
- Admission uses 1,000 total games and each row’s actual qualifying count.
  A mechanic that ends games early can leave late intervals too wide to pass;
  zero qualifying observations always fail.
- The new field's default must keep old behaviour exactly.
- Tests that use the hero can break, for example the cheat stories in
  `NegativeExamples.lean`. Update the test data so the test keeps its point;
  keep the test.

Add tests next to the code:

- The mechanic fires when on, and nothing changes when off (`#guard` or `example`).
- **Agreement**: run [`agree.lean`](agree.lean) with the mechanic on
  (`lake exe agree`). It compares the
  model's death chance for a fight with `validationGames` simulated fights,
  using the admission round limit and confidence level. Add one fight from
  each target story to `cases`. Every line must say `ok` (the model's chance
  is inside the simulation's 90% interval).

Write a line to the play log when the mechanic fires, so the player sees it.

Done when `lake build` passes and all tests pass.

### 3. Screen fairness

Run [`screen.lean`](screen.lean) from the repo root:

```
lake env lean .agents/skills/add-mechanic/screen.lean
```

It plays every adventure in `statisticalCandidates` the same way admission does,
with its own seed and the same fixed 1,000-game batch. Each row shows its
qualifying count, interval, policy band, and `ok`, `FAIL`, or `NO DATA`.
`ABORTED` means a fight hit the round limit or a game was invalid.

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
points of margin from each nontrivial policy bound. The margin is an
exploratory design buffer, not an additional confidence guarantee.

Done when the screen passes for every target. If three different
counter-mechanics fail, stop and report the numbers to the user.

### 5. Freeze, then admit once

Tune only with the screen. The validation seed is a held-out test: it counts
only if you look at it after the mechanics are final. Freeze the mechanics, then
run:

```
make check
make validate
```

`make check` builds and replays every proof in the kernel; it fails on `sorry`
and on new axioms. `make validate` runs admission on the Lighthouse with the fixed
validation seed and prints each row, then `ACCEPTED` or `NOT ADMITTED`.

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
  The build checks that the recorded counts match the current fixed batch.

## Report

Tell the user, briefly:

- The mechanic as built, in one sentence with numbers.
- Each open choice you decided, and why it is the most fun.
- The counter-mechanic, if any, and why it was needed.
- Before and after screen numbers per target, for the rows that moved.
- The agreement test results.
- The admission result per adventure, and the axiom list.
- Anything you had to ask about or could not do.
