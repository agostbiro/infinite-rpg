# Probability and balance

Edit the defaults in `Rpg/Probability/Weibull.lean`:

- `weibullRetention = 19/20` (q).
- `weibullShape = 2` (positive integer shape; 2 means the danger rises over the turns).
- `balanceTolerance = 1/5` (twenty percentage points of absolute error).

These are design choices, not measured or standard RPG parameters. They were picked
on the screening seed (1) so that the Lighthouse passes and an Adventure with no deaths
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
old solver on the Lighthouse Fights. This was a one-off check in the merge, not a build test. Exact rational state enumeration is expensive: one Lighthouse
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
qualifying count from a fixed batch of 1,000 games to construct an exact binomial
interval, enclosed by outward-rounded rational endpoints.
Admission requires the whole interval inside `[w_t - tolerance, w_t + tolerance]`.
The first-turn row uses target `1 - S(1)` to reject immediate-death loopholes.

`StatisticalCandidate.balanced` proves per-row interval coverage and a false-acceptance
bound for the entire finite decision under the explicitly accepted binomial
sampling model. With the current constants, each risk is at most 5%.
This does not assert simultaneous 95% coverage of all displayed intervals.
There is no requirement or claim about times beyond the selected horizon.
Lighthouse and every Wish use `H=5`.

Live changes also use `H=5`, starting from the adventure beginning with the updated rules
and the same original Weibull targets. `StatisticalCandidate.balancedAt` uses the actual per-attempt error allowance.
`RetryTree.balanced` proves a finite adaptive retry bound with decreasing allowances whose
total is at most 5%. See [live rule changes](live-rule-changes.md).

With shape 2, the targets rise from 5% on turn 1 to 27% on turn 6. The tolerance is
20 percentage points, so the first three rows only cap the risk, and from turn 4 on each
row also has a lower edge above 0. An Adventure where the Character never dies fails. It does not guarantee victory, behavior under
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
`Story.lean`, and its definition or certification. Lighthouse owns Mara, the
wreckers, and Hollis. The deliberately illegal
creature and story fixtures also live under Lighthouse, in `NegativeExamples.lean`.

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
The Lighthouse and every Wish go through the same `admitWithSeed`.

Live changes use `WorldChange.Prepared.admit`. Its certificate also binds the observations
to the updated adventure from its beginning and the error allowance. `Prepared.preserves_core` proves that the
patch changes only the adventure equipment/effect fields of `RuleSet`.

See [statistical confidence](statistical-confidence.md) for the theorem, accepted
sampling assumptions, fixed game batch, and Lighthouse's recorded results. The
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
