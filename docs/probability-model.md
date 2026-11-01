# Probability and balance

Every Adventure has a difficulty level: easy, medium, or hard. An Adventure with no level is
medium. Each level is a policy in `Rpg/Probability/Weibull.lean` (`DifficultyLevel.policy`):

- `DifficultyLevel.retention` (q): 993092495/10^9 (easy), 988032459/10^9 (medium),
  977237220/10^9 (hard). Each q is `p^(1/100)` rounded down to 9 places, where p is the chance to
  be alive after 10 turns: 50%, 30%, or 10%.
- `difficultyShape = 2` (positive integer shape; 2 means the danger rises over the turns).
- `difficultyTolerance = 1/20` (five percentage points of absolute error).

The old policy, `defaultPolicy`, stays in the same file: `weibullRetention = 19/20`,
`weibullShape = 2`, and `balanceTolerance = 1/5` (twenty percentage points). Only the test
Adventure uses it, as an exemption, because it fails the medium curve (see item 1 in
[follow-ups](follow-ups.md)).

These are design choices, not measured or standard RPG parameters. The old values were picked
on the screening seed (1) so that the earlier built-in Adventure (now the test Adventure) passes
and an Adventure with no deaths
fails; then the fixed validation seed was run once (see ADR 0004). The
positive-integer type-I discrete Weibull target has `P(T > t) = q^(t^shape)`.
This is a one-turn shift of the zero-based distribution documented by
[NIST](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/diwcdf.htm).
Retention controls the time scale without irrational exponential arithmetic.
Integer shapes and rational retention keep finite calculations exact; fractional
shape parameters are not supported by this implementation.

## Time and graph states

One turn is one scene choice. A fight, including all its rounds, consumes that
choice's turn. Combat rounds are **not** extra scene turns. Scene choices are uniform over the available options. On each turn of a Fight,
the model's Player picks Attack, All-Out Attack, or All-Out Defense with chance 1/3
each, then a living target uniformly (`heroPolicy`; the simulator uses `pickManeuver`). Dice are modeled
as independent, fair d6; the seeded game RNG is not proved equivalent to IID dice.
Human players are still free to choose; the certificate concerns this uniform
policy, not every possible player strategy.

`adventureGraph rules hero story` derives the graph from the adventure’s rules,
character, and story. The playable definition owns all three; there is no implicit
global character or selected ruleset.
Authors do not supply fight probabilities. A scene node contains both its scene
ID and remaining HP. Roll outcomes use the existing success-roll rules. Fight
outcomes use the engine's shared `attackWith`, `heroTurnWith`, and `foeTurnsWith` functions,
in the same turn order as play (`beforeCharacter`, the Character, `afterCharacter`), including
dodge, initiative, multiple foes, armor, and critical results. A fight win has
separate edges for different remaining HP. Death and successful endings are
separate absorbing nodes. Nonterminating combat has its own absorbing `stalled`
node, counted as still active rather than as a win or death.

For a change during play, the admission graph starts at the updated adventure's original
start and full initial HP, with all new equipment and combat effects applied from turn zero.
The played game keeps its actual checkpoint. The separate `continuationGraph` and
`remainingRoundWith` helpers can analyze or simulate a paused Fight without repeating
completed enemy turns; they are not the starting point for live-change admission.
No new probabilities are supplied by the DM.

A round can change the Character's maneuver with no HP loss. So the combat solver
works on a group: every state that rounds reach from a state with no HP loss. The
states of a group differ only in the Character's last maneuver, so a group has at most
3 states. The solver writes one linear equation for each state of the group and solves
them exactly (Gauss-Jordan elimination over rationals). Every way out of a group loses
HP, so the solver recurs on strictly decreasing total living HP. A group that can never
lose HP is `stalled`. It memoizes solved states. There is no imposed combat round limit.
With the policy "always Attack" (`attackOnlyPolicy`), the solver gave exactly the odds of the
old solver on the Fights of the earlier built-in Adventure (now the test Adventure). This was a one-off check in the merge, not a build test. Exact rational state enumeration is expensive: one such
Fight takes minutes in the interpreter. Do not assume large fights are cheap to analyze.

## Meaning of `balanced`

The shared theorem is finite statistical confidence. For a preselected positive
horizon `H`, it covers first-turn death and, for `0 <= t < H`,

```
p_t = E[1{death at t+2} | game active at t]
w_t = (S(t+1) - S(t+2)) / S(t),  S(t) = q^(t^shape).
```

The expectation is of a death indicator, not a death time. Completed successful
games are excluded from the conditioning event. Each row uses its actual
qualifying count from a fixed batch of 1,200 games (`difficultyGames`) to construct an exact binomial
interval, enclosed by outward-rounded rational endpoints.
Admission requires the whole interval inside `[w_t - tolerance, w_t + tolerance]`.
The first-turn row uses target `1 - S(1)` to reject immediate-death loopholes.

`StatisticalCandidate.balanced` proves per-row interval coverage and a false-acceptance
bound for the entire finite decision under the explicitly accepted binomial
sampling model. With the current constants, each risk is at most 5%.
This does not assert simultaneous 95% coverage of all displayed intervals.
There is no requirement or claim about times beyond the selected horizon.
The test Adventure and every Wish use `H=5`.

Live changes also use `H=5`, starting from the adventure beginning with the updated rules
and the Weibull targets of the game's own policy. A change cannot change the policy. `StatisticalCandidate.balancedAt` uses the actual per-attempt error allowance.
`RetryTree.balanced` proves a finite adaptive retry bound with decreasing allowances whose
total is at most 5%. See [live rule changes](live-rule-changes.md).

With shape 2, the targets rise over the turns. On medium they rise from 1.2% on turn 1 to 11.1%
on turn 6 (easy: 0.7% to 6.9%; hard: 2.3% to 18.2%). The tolerance is 5 percentage points, so the
first rows only cap the risk, and the later rows also have a lower edge above 0 (from turn 5 on
easy, turn 3 on medium, and turn 2 on hard). An Adventure where the Character never dies fails. It does not guarantee victory, behavior under
every player strategy, or closeness of the entire lifetime distribution to a
Weibull law. `checkBalanceThrough` remains an exact finite diagnostic for small
graphs; admission uses the proved exact-binomial confidence protocol.

## Expectations

`Graph.expectedTimeToTermination` is the supremum of the tail sums
`sum (t < n) P(game active at t)`. It counts turns until either success or death.

`Graph.expectedTimeToDeath` is the supremum of
`sum (t < n) P(not dead by t)`. Successful endings never die, so positive
probability of successful completion makes this expectation infinite.

`Graph.expectedTimeToDeathGivenDeath` supplies a positive-event condition and the
supremum of `E[T | death by n]`. This conditional expectation is undefined when
there is no chance of eventual death. `conditionalDeathPartial` returns `none`
when its conditioning event has probability zero.

`ExtendedExpectation` represents these exact, possibly infinite quantities by
their rational upper bounds. It is a mathematical definition, not a numerical
infinite-series evaluator. `terminationPartial`, `deathPartial`, and
`conditionalDeathPartial` are executable finite-horizon calculations. A finite
cutoff must not be reported as the exact expectation without an additional proof.

## Authoring and enforcement

Each `Rpg/Adventures/<Name>/` folder contains `Rules.lean`, `Characters.lean`,
`Story.lean`, and its definition or certification. The test Adventure (`TestAdventure/`) owns
Mara, the bandits, and the bandit chief. The deliberately illegal
creature and story fixtures also live there, in `NegativeExamples.lean`.

`Rpg/RuleSet.lean` defines the common rule interface. `Rpg/Rules.lean` provides
reusable GURPS Lite defaults. Each adventure owns its selected `RuleSet`, including
build constraints, success rolls, skill and point calculations, HP, damage,
armor, dodge, and initiative settings. The game still uses the shared GURPS-style
d6/attack/dodge turn structure; this is not an arbitrary combat-language interpreter.

`AdventureDefinition` (in `Rpg/Spec.lean`) bundles the rules, character, and raw story,
plus **both** `LegalCharacter rules hero` and `LegalAdventure rules hero story`.
The graph is derived from those exact values, and `Game.new` takes the same record,
so play uses the same rules.
Changing rules or characters requires rechecking their dependent certificates.
The shared Weibull balance policy remains fixed across adventures.

Each adventure supplies a `StatisticalCandidate` with its definition, a positive
finite horizon, and the specialized theorem `balanced`. Register candidates in
`Rpg/Catalog.lean`; the runtime `admitStatistically` gate collects source-bound
counts and requires every interval to fit the shared Weibull band. Its resulting
`StatisticalAdventure` carries both `balanced` and the passing observation evidence.
The test Adventure and every Wish go through the same `admitWithSeed`.

Live changes use `WorldChange.Prepared.admit`. Its certificate also binds the observations
to the updated adventure from its beginning and the error allowance. `Prepared.preserves_core` proves that the
patch changes only the adventure equipment/effect fields of `RuleSet`.

See [statistical confidence](statistical-confidence.md) for the theorem, accepted
sampling assumptions, fixed game batch, and the recorded results. The
admission interface has no graph-validity or tail premises. The probability and
lifetime fixtures remain, along with interval, boundary, censoring, and sampling
model tests.

## Trusted surface and validation

The probability specification, graph builder, distribution operations, and
combat elimination algorithm are part of the trusted definitions. Sharing the
engine's attack and actor-turn code prevents independent copies of damage rules,
but there is not yet a general theorem proving the elimination algorithm equals
the infinite stochastic operational execution. The ideal sampling correspondence
is an accepted assumption of `balanced`, including the idealization of SplitMix64 and
modulo-based choices.

All stated theorems use kernel proofs; none use `sorry`, additional axioms, or
`native_decide`. Compiled `#guard` checks are regression tests, not theorems.
`lake check` provides an additional proof replay, but requires Linux namespaces
and does not run on macOS. A normal `lake build` still kernel-checks the theorem
declarations.
