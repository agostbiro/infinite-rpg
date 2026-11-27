# Exact Fight exit laws

The **exit law** of a Fight is the chance of each result when the Character enters the Fight
with a given HP: a win with each number of HP left, or death. The player is `heroPolicy`
(`Rpg/Probability/Combat.lean`) and the dice are fair. This note tells how the combat check now
computes the exit laws fast, and how an exact Markov model of the Adventure, such as the one in
PR agostbiro/infinite-rpg#4, can use them in place of the sample games.

## What Lean proves

`certify` (`Rpg/Probability/StatisticalAdmission.lean`) gives a `CertifiedAdventure`, or `none`
if a Fight fails the check. For each
Fight in the story and each entry HP from 0 to full HP, the value
`CertifiedAdventureCombat.exitLaw foes hf hp hi` (`Rpg/Probability/AdventureCertificate.lean`) is
the exit law. The proof `hi` says that `hp` is at most full HP, because only those entry HPs are
checked. `CertifiedEncounter.exitLaw?` gives `none` above full HP. Four theorems are about it:

| Theorem | What it says |
| - | - |
| `CertifiedEncounter.exitLaw_valid` | The weights are not negative, and their sum is 1. |
| `CertifiedEncounter.exitLaw_stalled` | The result `stalled` has weight 0. Each Fight ends in a win or a death. |
| `CertifiedEncounter.exitLaw_bounds` | For each set of results and each `n`: the chance to end in the set within `n` rounds is at most the exit law's weight of the set, and that weight is at most this chance plus the chance that the Fight is still going after `n` rounds. |
| `CertifiedEncounter.exitLaw_exact` | For each set of results, the weight is the limit of the chance to end in the set within `n` rounds: for each `delta > 0`, from some `N` on, the weight is at least that chance and at most `delta` above it. |

Comparator pins these facts as `admitted_exit_law`, `admitted_exit_law_exact` and
`admitted_exit_law_valid`. `exitLaw_exact` follows from `exitLaw_bounds` and the stopping
certificate: after its horizon, the chance that the Fight is still going is at most `delta`. The probabilities are about `combatProcess`: rounds of
`roundDistribution`, which `combat_full_dice` ties to the Engine with full fair dice.

## Timings

On Lafayette at Barren Hill, all Fights, all 12 entry HPs (0 to 11). The machine has 14 cores.
"Before" is commit `2d4b8cf`, which is one core only.

| Fight | States | Before: solve | Before: check | After: solve | After: check |
| - | -: | -: | -: | -: | -: |
| Grenadier 1 | 231 | 3.4 s | 6.9 s | 0.03 s | 0.01 s |
| Dragoon Scout | 231 | 3.9 s | 7.5 s | 0.05 s | 0.02 s |
| Grenadier 1 and 2 | 7,623 | 281 s | 1,052 s | 1.3 s | 0.7 s |
| Loyalist Scout | 231 | 3.3 s | 6.5 s | 0.05 s | 0.02 s |
| Jäger 1 and 2 | 6,336 | 253 s | 864 s | 1.5 s | 0.8 s |
| Dragoon Sergeant | 396 | 9.5 s | 18.7 s | 0.08 s | 0.04 s |
| **All** | 15,048 | 555 s | 1,955 s | 3.0 s | 1.6 s |
| **Total wall time** | | **2,510 s (42 min)** | | **4.6 s** (36 s of CPU) | |

`lake exe profile-combat` prints the "after" numbers. Pinned to one core (`taskset -c 0`),
`make certify` takes 28 s on Lafayette, inside 3 minutes even on one core. No live change runs
`certify`, and a larger Adventure can take longer.

**Baseline.** `experiments/profile/exit-laws-2d4b8cf/` holds the exit laws of all six Fights at
every entry HP, as exact fractions. The solver of commit `2d4b8cf` made them, on the spec round,
before any code of this change existed. `make compare-exit-laws` checks that the new exit laws
are the same, weight for weight. It also fails if the folder does not hold exactly one file for
each Fight, and `--dump` cannot write into the folder that `--compare` reads. (A program at
`2d4b8cf` makes the files with the same text form as `--dump`.)

**Larger Fights.** The cost grows fast with the number of Creatures: one round with 4 Creatures
takes about 25 times as long as one with 2. A weapon that hits every Creature (the flamethrower)
grows it more: each round makes one result for each mix of injuries. `solveFight` has a budget
(`SolveBudget`). Above it, the solver gives up, the check fails, and the Fight is rejected. That
is sound. On the paused Fights in the table below, the most memory used was 334 MB. `make certify`
on Lafayette uses about 610 MB.

* Before it computes any round, the solver bounds how many results the round makes before
  they are merged (`roundSizeBound`). For each pair of Fighters, `attackBounds` finds each damage
  bonus and DR that one attack can have, over every maneuver of the two (`injuryTerms`). A combat
  rule reads HP only through the `wounded` and `desperate` triggers, so it tries one HP for each
  case of the two triggers, three per Fighter (`hpSamples`), not every HP. A test compares this
  with a search over every HP. For each damage bonus and DR it counts the different injuries over
  the sums of the damage dice (`injuryCount`). It computes no attack. The bound is tested, not
  proved. It holds if the combat rules read only HP and maneuvers, as they do now, and if the turn
  order names each Creature once. Tests compare it with real rounds that are not merged. The largest bound on
  Lafayette is 1,421. A wrong bound can only make the solver slow or reject a Fight. It cannot
  make a wrong exit law pass the check.
* The solver rejects the Fight if one round is above 200,000. A Fight with such rounds could
  compute at most 50 of them within the work limit below, too few to finish. It puts the states
  in batches, one round per state, and the bounds of the rounds in one batch add up to at most
  1 million (`planRounds`). `solveChecked` is the one solver call that the check and
  `profile-combat` use.
* It also stops at 60,000 states, 1.5 million round results in memory, or 10 million for the
  sum of the bounds of all rounds it computed (the work). On Lafayette, Grenadier 1 and 2 has
  the most states (7,623), and Jäger 1 and 2 has the most work (2.2 million). The most round
  results in memory is about 450,000. So the limits are 3.3 to 8 times as large. The solver
  tests the state limit each time it finds a new state, also while it adds the starts. Each entry
  HP gives a start of its own, so `certifyEncounter` rejects a Character with more than 20,000 HP
  (with a living Creature) before it makes the starts. It adds a batch to the work before it
  tests the work limit, so the work never goes above it. It tests the memory limit before each
  batch, so one batch (at most 1 million results) can go above that limit.
* The work limit makes a rejection fast. A large Fight gives up after a small part of its
  rounds, not after it fills memory.
* The checker computes the rounds again, one round at a time on each core. So the rounds that
  the checker computes take at most one round of memory per core. The checker also holds the
  whole witness, whose exact answers can have very large denominators. With the default budget,
  each round is at most 200,000 results by `roundSizeBound`, which is tested, not proved.
* `certifyContinuation` checks the paused round with the same bound before it computes it. The
  paused round counts against the budget as one full round: against the round and batch limits,
  and against the work limit. Its results stay in memory, so they also count against the memory
  limit. The later rounds get the work and the memory that are left. It then computes the paused round with the fast attack and merges after each turn
  (`fastRemaining`), like the full rounds. `fastRemaining_expect` proves that it has the odds of
  the spec's paused round.
* When the check of a paused Fight fails, `checkContinuation` gives the reason: one round is too
  large, the solver is over its budget, or the check found no proof that the Fight ends. The
  author of the live change sees a message that names the Creatures. A paused Fight keeps its
  Creatures and the requested effects stay fixed, so the message suggests only what can change:
  the counter-rules, or a change after the Fight ends. Counter-rules that change damage or armor
  change the size of the check in either direction: more armor can merge injuries, more damage
  can spread them. So the server treats no size failure as final, and the Dungeon Master can
  revise the counter-rules. One test shows a counter-rule that makes the bound larger; no test
  shows one that brings a rejected Fight under the limit. The server runs this check before it
  spends a validation batch (`Prepared.checkPaused`), so a proposal that this check rejects
  spends no part of the error allowance. A proposal that reaches the validation batch spends its
  part, also if it then fails. The check uses no dice, reads no Scene, and reads no name or
  description of a rule, so the server remembers the equipment and the side, trigger and numbers
  of the rules of each proposal that failed it (`combatKey`). It does not check them again, also
  in a proposal that changes only Scenes or the wording of a rule, and the tuning of the
  counter-rules skips them. The server also keeps each paused Fight that passed the check. A later
  proposal with the same equipment and rules reuses it (`Prepared.reuseCheckpoint`), and gets a
  fresh validation batch. `Prepared.game_rules_phase` proves that the two proposals have the same
  paused point. If the
  change runs out of proposals and the last one failed this check, the last step says so, and
  that the change can be asked for again after the Fight ends (`changeOutOfBudget`).

Measured with `lake exe profile-combat --grenadiers N` (add `--flamethrower` to give Lafayette
a flamethrower, `--dice D` to give its weapon `D` damage dice, and `--st S` to give each
Grenadier ST `S`; a Grenadier has ST 11). The 1-core
column uses `taskset -c 0`. In the check at every entry HP, two Grenadiers are certified up to
ST 16 and rejected from ST 17, with or without the work limit. In the paused check below, they are
certified up to ST 18 and rejected from ST 19. A check that passes can take longer than one that
rejects: up to 35 s on one core at ST 18.

| Fight | 14 cores | 1 core | Memory | Result |
| - | -: | -: | -: | - |
| 2 Grenadiers, paused | 1.0 s | 6.6 s | 180 MB | certified |
| 2 Grenadiers with ST 16, paused | 3.5 s | 25 s | 330 MB | certified |
| 2 Grenadiers with ST 17, paused | 4.4 s | 30 s | 334 MB | certified |
| 2 Grenadiers with ST 18, paused | 5.0 s | 35 s | 320 MB | certified |
| 2 Grenadiers with ST 19, paused | 2.3 s | 17 s | 264 MB | rejected (over budget) |
| 2 Grenadiers with ST 20, paused | 2.4 s | 18 s | 270 MB | rejected (over budget) |
| 3 Grenadiers, paused | 2.2 s | 16 s | 210 MB | rejected (over budget) |
| 4 Grenadiers, paused | 1.8 s | 13 s | 140 MB | rejected (over budget) |
| 2 Grenadiers, flamethrower, paused | 1.4 s | 9.3 s | 210 MB | rejected (over budget) |
| 2 Grenadiers with ST 6, flamethrower, paused | 3.5 s | not measured | 221 MB | certified |
| 3 Grenadiers, flamethrower, paused | 0.001 s | not measured | 167 MB | rejected (round bound 3.7 million) |
| 4 Grenadiers, flamethrower, paused | 0.01 s | 0.01 s | 105 MB | rejected (round bound 418 million) |
| 4 Grenadiers with ST 1, flamethrower, paused | 0.01 s | 0.01 s | 105 MB | rejected (round bound 668,169) |
| 4 Grenadiers, flamethrower with 6 dice, paused | 0.01 s | 0.01 s | 105 MB | rejected (round bound 5.2 billion) |

The times are for the call `certifyContinuation` only. The memory is the most that the whole
run used, which also checks the Fight at every entry HP first.

With no budget, the Fight against 2 Grenadiers with a flamethrower has 13,959 states and 4.2
million round results, and the solver alone takes 120 s and 815 MB.

Without the budget, a paused Fight with 4 Creatures ran out of memory and stopped the server
process. Before this change such a Fight never finished at all. To certify Fights with 3 or more
Creatures needs a faster round or a smaller state space, not a larger budget.

## Where the time went, and what changed

1. **One attack walked about 2,000 dice paths.** `roundDistribution` runs the Engine's
   `attackWith` on each sum of the attack, Dodge and damage dice, and builds Reports on each
   path. A round took 23 ms with one foe and 200 ms with two. `injuryDistribution`
   (`Rpg/Probability/FastCombat.lean`) computes the same injury law from three small tables. It
   groups the attack rolls by result, and it rolls the Dodge and the damage once.
2. **`collect` compares each pair of states.** With two foes a round has up to 340 results.
   `Distribution.sortCollect` sorts by a key made from HP and maneuvers, then merges
   neighbours. With both changes, a round takes 0.3 ms with one foe and 3–4 ms with two.
3. **The witness was a list.** Each lookup was a linear search with a full compare of the
   states. The witness is now a `Std.HashMap`.
4. **The checker computed each round three times.** `CombatWitness.rowCheck` computes it once.
5. **The solver kept long unmerged lists** of results through the elimination. It now merges
   equal results as it adds them (`Weighted.addScaled`). The numbers are exact and large: the
   Jäger Fight has denominators of up to 1,067 digits.
6. **Everything ran on one core.** `solveFight` finds all reachable states with their rounds,
   then solves the groups level by level, by total HP. Groups at the same level do not depend
   on each other. `parallelAll` checks the rows in pieces.

The checker does not trust the new code. The fast round is not the spec round. These facts
connect the two:

* `fastRound_expect`: for every observable of the state after a round, `fastRound` and
  `roundDistribution rules heroPolicy` give the same expected value. The proof goes through
  `round_forgets` (`Rpg/Probability/RoundRefinement.lean`), which `DiceRefinement.lean` now uses
  too, for full fair dice.
* `StoppingProcess.SameOdds` (`Rpg/Probability/Stopping.lean`): two processes with the same end
  states and the same one-step expected values have the same `unfinished` and `eventBy` at
  every horizon. The certificate is checked against `fastProcess`, and `fastProcess_sameOdds`
  carries each result to `combatProcess`. `fastContinuation_sameOdds` does the same for a paused
  Fight in a live change, with `fastRemaining_expect` for the paused round.
* `parallelAll_sound`: `(Task.spawn f).get` is `f ()` in the logic, so if the parallel check
  passes, every row passes. That is the direction that the soundness of the checker needs.

The solver is still untrusted, and a wrong answer fails the check. The text of the old
Comparator statements did not change, and all statements use only `propext`, `Quot.sound` and
`Classical.choice`. Their conclusions are still about `combatProcess`. But the hypothesis
`CertifiedFight` now names the fast definitions (`fastProcess`, `fastRound`,
`injuryDistribution`, `sortCollect`, `stateKey` and the others in `FastCombat.lean`), and
`CertifiedContinuation` names `fastRemaining`. They
decide only which certificates exist, not what the theorems conclude, so a reviewer need not
read them for soundness. Which Fights get a certificate depends on the solver and its budget.

**Termination witness.** The check keeps the expected-rounds witness. The rounds equation is
one number per state. The outcome equations are about 13 numbers per state. So a path
certificate, like `Paths.terminates` in PR agostbiro/infinite-rpg#4, would save only a small part
of the time, and it needs a new proof. The witness also gives `finishes_with_high_probability`,
an explicit horizon for each error allowance.

## How the exit laws plug into the model of PR agostbiro/infinite-rpg#4

PR agostbiro/infinite-rpg#4 has an adventure graph whose nodes hold the event and the
Character's HP. A resolved Fight is one adventure event. `adventureGraph`
(`Rpg/Probability/Graph.lean`) in this repo has the same shape: one turn is one scene choice,
including its whole Fight. The steps:

1. **Certify once per admission.** Run `certify` (or `certifyAdventureCombat` on the
   candidate's definition) after the Wish or the live change is built. It gives the exit law of
   each Fight at each entry HP. It is about 5 s on Lafayette. A Fight over the solver budget
   has no exit law, so admission must reject the Adventure. It must not put `stalled` in
   its place: an exact check would then see a Fight with no deaths. The spec odds
   (`checkedCombat`) use no budget, so only the checker can reject.
2. **Build the combat edges from the exit laws.** For a choice `.fight foes onWin` at a node
   with HP `h`, the edges are `exitLaw foes hf h hi`, mapped by result: `.won hp` goes to
   `arrive story onWin hp`, and `.died` goes to Lose. This is the formula K(s, a, v) of section 4
   of PR agostbiro/infinite-rpg#4. `exitLaw_stalled` proves that no edge goes to `stalled`.
   `outcomeEdges` now calls `checkedCombat`, which solves the Fight again for each node. The
   exit-law table removes that work.
3. **Use the theorems for the model's premises.** Section 3 (each combat terminates) is
   `admitted_combats`. Section 4 (a combat can be replaced by its exit law) needs the exit
   law to be the true law of the Fight at the actual entry HP. That is `exitLaw_exact`
   (`admitted_exit_law_exact` in Comparator).
4. **Live changes.** A change during play keeps the paused Fight, with its wounds, maneuvers
   and remaining turn order. `certifyContinuation` now uses the same fast path. Its witness
   gives the answer of each state after the paused round. The exit law of the paused Fight is
   the law of the paused round followed by those answers. No definition or theorem gives this
   exit law yet: `CertifiedContinuation` proves only that the paused Fight ends with probability
   one. A model that checks from the current state (section 5 of PR agostbiro/infinite-rpg#4)
   needs that definition and an analogue of `exitLaw_exact`.
5. **Numbers.** The exit laws are exact rationals with large denominators. An exact
   adventure-level solve multiplies them, so it should merge equal nodes after each step, as
   `Graph.after` does with `collect`.

Not done here: the server still admits with the 1,200 sample games, and does not call `certify`.
PR agostbiro/infinite-rpg#4 itself is not ported (Lean 4.33, a Python server, and a simpler
combat with two fighters and two maneuvers).
