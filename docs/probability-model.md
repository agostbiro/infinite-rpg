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

## Meaning of the fairness proof

`isFair policy graph` requires normalized transition probabilities, absorbing
terminal states, an initially active game, and a first-turn death probability
within tolerance of `1 - q`. The first-turn check closes the loophole where a
certain death on turn one would evade a turn-two test.

For **every** `t` with positive active probability, it also requires:

```
abs(P(death exactly at t+2 | game active at t)
    - (S(t+1) - S(t+2)) / S(t)) <= tolerance
```

Here `S(t) = q^(t^shape)`. This is a conditional probability (the expectation of a
death indicator), not an expected time. It means death **at** turn `t+2`, not
any death within the next two turns. Completed successful games are excluded
from the conditioning event. Times with zero active probability are skipped;
no division by zero is treated as a certificate.

This is a pointwise absolute-error criterion on the stated probabilities. It is
not a guarantee about every player strategy, overall win rate, or a distance
between the entire lifetime distribution and a Weibull law.

`checkFairnessThrough` checks policy validity, the initial active state, the
first-turn guard, and the two-turn bounds at finitely many times. It returns
structured failures, including the actual and target probabilities. It does not
check normalization over the entire graph. Passing that
finite diagnostic is not an all-time proof. Changing any default constant
invalidates certificates that no longer prove the shared policy. The kernel
must recheck them; authors cannot override policy parameters per story.

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
from those exact values, and `playCertified` passes the same rules to the engine.
Changing rules or characters requires rechecking their dependent certificates.
The shared Weibull fairness policy remains fixed across adventures.

An exact `Probability.CertifiedAdventure` additionally requires a proof of
`isFair defaultPolicy (adventureGraph rules hero story)`. Harbor uses that path.
Lighthouse uses a separate `StatisticalCandidate` and runtime
`admitStatistically` gate. It must pass a fresh source-bound run of the fixed
confidence protocol before appearing in the menu. The menu labels the two
kinds of evidence separately.

See [statistical confidence](statistical-confidence.md) for the precise Lean
probability theorem, model assumptions, frozen parameters, held-out results,
and the remaining graph-to-model proof boundary. The original all-time
`isFair` predicate has not been replaced with a simulated Boolean.

The probability examples include exact fairness rejection tests, source-specific
rule tests, and exact lifetime proofs. The confidence tests exercise numerical
budget validity, clipping, boundary rejection, a concrete valid sampling law,
incomplete sampling, and abort handling.

## Trusted surface and validation

The probability specification, graph builder, distribution operations, and
combat elimination algorithm are part of the trusted definitions. Sharing the
engine's attack and actor-turn code prevents independent copies of damage rules,
but there is not yet a general theorem proving the elimination algorithm equals
the infinite stochastic operational execution. Likewise, there is no theorem
relating ideal IID dice to SplitMix64. Do not claim either result from `isFair`.

All stated theorems use kernel proofs; none use `sorry`, additional axioms, or
`native_decide`. Compiled `#guard` checks are regression tests, not theorems.
The seeded engine refactor was compared with its previous implementation on
1,024 rounds, checking HP, combat logs, and final RNG state. `lake check` provides
an additional proof replay, but requires Linux namespaces and does not run on
macOS. A normal `lake build` still kernel-checks the theorem declarations.
