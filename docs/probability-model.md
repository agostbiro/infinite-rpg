# Probability and fairness

Edit the defaults in `Rpg/Probability/Weibull.lean`:

- `weibullRetention = 4/5` (q).
- `weibullShape = 1` (positive integer shape).
- `fairnessTolerance = 1/5` (twenty percentage points of absolute error).

These are initial design choices, not measured or standard RPG parameters. The
positive-integer type-I discrete Weibull target has `P(T > t) = q^(t^shape)`.
This is a one-turn shift of the zero-based distribution documented by
[NIST](https://www.itl.nist.gov/div898/software/dataplot/refman2/auxillar/diwcdf.htm).
Retention controls the time scale without irrational exponential arithmetic.
Integer shapes and rational retention keep finite calculations exact; fractional
shape parameters are not supported by this implementation.

## Time and graph states

One turn is one scene choice. A fight, including all its rounds, consumes that
choice's turn. Combat rounds are **not** extra scene turns. Scene choices and
combat target choices are uniform over the available options. Dice are modeled
as independent, fair d6; the seeded game RNG is not proved equivalent to IID dice.
Human players are still free to choose; the certificate concerns this uniform
policy, not every possible player strategy.

`adventureGraph rules hero story` derives the graph from the adventure’s rules,
character, and story. The playable definition owns all three; there is no implicit
global character or selected ruleset.
Authors do not supply fight probabilities. A scene node contains both its scene
ID and remaining HP. Roll outcomes use the existing success-roll rules. Fight
outcomes use the engine's shared `attackWith` and `takeTurnWith` functions, including
dodge, initiative, multiple foes, armor, and critical results. A fight win has
separate edges for different remaining HP. Death and successful endings are
separate absorbing nodes. Nonterminating combat has its own absorbing `stalled`
node, counted as still active rather than as a win or death.

The combat solver eliminates no-change rounds using `1 / (1 - pStay)` and recurs
on strictly decreasing total living HP. It memoizes completed combat states.
There is no imposed combat round limit. A defensive branch reports nondecreasing,
non-self transitions as stalled; existing combat only removes HP. Exact rational
state enumeration is expensive: the exploratory Lighthouse two-foe calculation
was stopped before completion. Do not assume large fights are cheap to analyze.

## Meaning of `fair`

The shared theorem is finite statistical confidence. For a preselected positive
horizon `H`, it covers first-turn death and, for `0 <= t < H`,

```
p_t = E[1{death at t+2} | game active at t]
w_t = (S(t+1) - S(t+2)) / S(t),  S(t) = q^(t^shape).
```

The expectation is of a death indicator, not a death time. Completed successful
games are excluded from the conditioning event. Each observed frequency has an
exact rational interval of radius `confidenceEpsilon`, clipped to `[0,1]`.
Admission requires the whole interval inside `[w_t - tolerance, w_t + tolerance]`.
The first-turn row uses target `1 - S(1)` to reject immediate-death loopholes.

`StatisticalCandidate.fair` proves per-row interval coverage and a false-acceptance
bound for the entire finite decision under the explicitly accepted binomial
sampling model. With the current constants, each risk is at most 0.1%.
This does not assert simultaneous 99.9% coverage of all displayed intervals.
There is no requirement or claim about times beyond the selected horizon.
Lighthouse uses `H=6`; Harbor uses `H=1`.

The chosen tolerance is 20 percentage points, so the current geometric policy
mainly imposes upper risk caps. It does not guarantee victory, behavior under
every player strategy, or closeness of the entire lifetime distribution to a
Weibull law. `checkFairnessThrough` remains an exact finite diagnostic for small
graphs; admission uses the cheaper proved confidence protocol.

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
wreckers, and Hollis; Harbor owns Iona. They use separate namespaces and Harbor
does not import Lighthouse's character definitions. The deliberately illegal
creature and story fixtures also live under Lighthouse, in `NegativeExamples.lean`.

`Rpg/RuleSet.lean` defines the common rule interface. `Rpg/Rules.lean` provides
reusable GURPS Lite defaults. Each adventure owns its selected `RuleSet`, including
build constraints, success rolls, skill and point calculations, HP, damage,
armor, dodge, and initiative settings. The game still uses the shared GURPS-style
d6/attack/dodge turn structure; this is not an arbitrary combat-language interpreter.

`Probability.AdventureDefinition` bundles the rules, character, and raw story,
plus **both** `LegalCharacter rules hero` and `LegalAdventure rules hero story`.
The earlier version accidentally omitted the character proof. The graph is derived
from those exact values, and `playStatistical` passes the same rules to the engine.
Changing rules or characters requires rechecking their dependent certificates.
The shared Weibull fairness policy remains fixed across adventures.

Each adventure supplies a `StatisticalCandidate` with its definition, a positive
finite horizon, and the specialized theorem `fair`. Register candidates in
`Rpg/Catalog.lean`; the runtime `admitStatistically` gate collects source-bound
counts and requires every interval to fit the shared Weibull band. Its resulting
`StatisticalAdventure` carries both `fair` and the passing observation evidence.
There is one admission path for Harbor and Lighthouse.

See [statistical confidence](statistical-confidence.md) for the theorem, accepted
sampling assumptions, fixed protocol, and Lighthouse's recorded results. The
admission interface has no graph-validity or tail premises. The probability and
lifetime fixtures remain, along with interval, boundary, censoring, and sampling
model tests.

## Trusted surface and validation

The probability specification, graph builder, distribution operations, and
combat elimination algorithm are part of the trusted definitions. Sharing the
engine's attack and actor-turn code prevents independent copies of damage rules,
but there is not yet a general theorem proving the elimination algorithm equals
the infinite stochastic operational execution. The ideal sampling correspondence is an accepted assumption of `fair`, including
the idealization of SplitMix64 and modulo-based choices.

All stated theorems use kernel proofs; none use `sorry`, additional axioms, or
`native_decide`. Compiled `#guard` checks are regression tests, not theorems.
The seeded engine refactor was compared with its previous implementation on
1,024 rounds, checking HP, combat logs, and final RNG state. `lake check` provides
an additional proof replay, but requires Linux namespaces and does not run on
macOS. A normal `lake build` still kernel-checks the theorem declarations.
