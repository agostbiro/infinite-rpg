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
`CertifiedAdventureCombat.exitLaw foes hf hp` (`Rpg/Probability/AdventureCertificate.lean`) is
the exit law. Three theorems are about it:

| Theorem | What it says |
| - | - |
| `CertifiedEncounter.exitLaw_valid` | The weights are not negative, and their sum is 1. |
| `CertifiedEncounter.exitLaw_stalled` | The result `stalled` has weight 0. Each Fight ends in a win or a death. |
| `CertifiedEncounter.exitLaw_exact` | For each result and each `n`: the chance of that result within `n` rounds is at most the exit law's weight, and the weight is at most that chance plus the chance that the Fight is still going after `n` rounds. |

Comparator pins these facts as `admitted_exit_law` and `admitted_exit_law_valid`.
`admitted_combats` (Comparator) says that each Fight ends with probability one. So the chance
that the Fight is still going goes to zero, and `exitLaw_exact` says that each weight is the
true probability of that result. The probabilities are about `combatProcess`: rounds of
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

`lake exe profile-combat` prints the "after" numbers. Pinned to one core (`taskset -c 5`),
`make certify` takes 28 s, so it fits inside the 3-minute live-change limit even on one core. With `--compare`, it also solves
each one-foe Fight with the old solver on the spec round. The exit laws are the same, weight for
weight, at every entry HP.

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
  Fight in a live change.
* `parallelAll_sound`: `(Task.spawn f).get` is `f ()` in the logic, so the parallel check means
  the same as `List.all`.

The solver is still untrusted, and a wrong answer fails the check. The text of the old
Comparator statements did not change, and all statements use only `propext`, `Quot.sound` and
`Classical.choice`. Their conclusions are still about `combatProcess`. But the hypothesis
`CertifiedFight` now names the fast definitions (`fastProcess`, `fastRound`,
`injuryDistribution`, `sortCollect`, `stateKey` and the others in `FastCombat.lean`). They
decide only which certificates exist, not what the theorems conclude. A reviewer of the
trusted surface should still read them.

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
   each Fight at each entry HP. It is about 5 s on Lafayette.
2. **Build the combat edges from the exit laws.** For a choice `.fight foes onWin` at a node
   with HP `h`, the edges are `exitLaw foes hf h`, mapped by result: `.won hp` goes to
   `arrive story onWin hp`, and `.died` goes to Lose. This is the formula K(s, a, v) of section 4
   of PR agostbiro/infinite-rpg#4. `exitLaw_stalled` proves that no edge goes to `stalled`.
   `outcomeEdges` now calls `checkedCombat`, which solves the Fight again for each node. The
   exit-law table removes that work.
3. **Use the theorems for the model's premises.** Section 3 (each combat terminates) is
   `admitted_combats`. Section 4 (a combat can be replaced by its exit law) needs the exit
   law to be the true law of the Fight at the actual entry HP. That is `exitLaw_exact` together
   with `admitted_combats`.
4. **Live changes.** A change during play keeps the paused Fight, with its wounds, maneuvers
   and remaining turn order. `certifyContinuation` now uses the same fast path. Its witness
   gives the answer of each state after the paused round. The exit law of the paused Fight is
   the law of the paused round followed by those answers. A model that checks from the current
   state (section 5 of PR agostbiro/infinite-rpg#4) can start from it.
5. **Numbers.** The exit laws are exact rationals with large denominators. An exact
   adventure-level solve multiplies them, so it should merge equal nodes after each step, as
   `Graph.after` does with `collect`.

Not done here: the server still admits with the 1,200 sample games, and does not call `certify`.
PR agostbiro/infinite-rpg#4 itself is not ported (Lean 4.33, a Python server, and a simpler
combat with two fighters and two maneuvers).
