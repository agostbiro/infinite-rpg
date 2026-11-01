# Statistical fairness confidence

## What is proved

`Rpg/Probability/Confidence.lean` defines the exact rational binomial expectation
recursively from independent Bernoulli trials. Lean proves its first and second
moments, the variance `n*p*(1-p)`, the bound `p*(1-p) <= 1/4`, and a Chebyshev
confidence inequality. It does not import an assumed confidence bound.

The theorem `fairnessConfidence` proves that the probability of accepting a
constraint outside its true allowed band is at most `delta`, provided

```
n / 4 <= delta * (n * epsilon)^2.
```

Acceptance checks that the full frequency interval, clipped to `[0,1]`, is inside
the allowed band. Overlap alone is insufficient. All comparisons used for
admission are exact rational arithmetic; Float values are display-only.

`familyFairnessConfidence` proves the joint guarantee when **every** constraint
must pass. If the actual family is unfair, at least one fixed constraint is
unfair, and approving the family entails falsely approving that constraint.
Thus the same error bound applies to the family without requiring independence
between rows. This is an intersection-union test, not a simultaneous-coverage
claim about every displayed interval.

The concrete theorem is `Rpg.Lighthouse.lighthouse_fairnessConfidence`. Its true
probabilities are derived from Lighthouse's own rules, hero, and story graph.
The fixed protocol constants are:

- `confidenceSamples = 160000` qualifying observations **per row**.
- `confidenceEpsilon = 1/25` (four percentage points).
- `confidenceDelta = 1/1000` (false acceptance at most 0.1% in the model).

`confidenceBudget` proves that these constants meet the inequality. The proof
uses only the standard Lean axioms, not `sorry`, new axioms, or `native_decide`.

## Model assumptions and scope

The probability theorem assumes a valid joint observation law whose row
marginals are binomial with the specified true probabilities. This encodes
independent trajectories, fixed parameters, and the first fixed number of
qualifying observations. It is a sampling-model hypothesis, not an assumed
confidence result. Rows may be correlated because they share game trajectories.

The implementation uses seeded SplitMix64. There is **no proof that this PRNG is
IID**, nor a complete proof that the executable sampler induces the graph's
probability law. The confidence theorem is rigorous within its explicit model;
this is not an unconditional, end-to-end software/randomness theorem.

The theorem bounds the procedure's false-acceptance probability. It does **not**
mean that a particular adventure has a Bayesian posterior probability of 99.9%
of being fair after seeing the sample, and does not turn a statistical pass into
an exact `isFair` proof.

Lighthouse's source-based `ranks_decrease` and `route_bound` proofs bound scene
routes by six choices; `zero_death_tail` proves that zero later death probability
fits the tuned policy. The additional theorem `allTimeFairnessConfidence` states
the stronger original all-time guarantee with explicit graph-normalization,
initial-state, and tail obligations. The complete mechanized bridge from the
route/compiler facts to those graph-CDF obligations remains outstanding.
Statistical admission therefore carries the checked observations and the
model-conditional risk theorem, rather than an exact `CertifiedAdventure`.

## Frozen experiment

The initial exploratory run used 100,000 games and seed 20261101. Under the old
policy (`q=0.99`, shape 2, tolerance 0.05), it found a clear estimated violation:
death at turn 5 conditional on activity at turn 3 was approximately 27.4%, while
the old upper allowance was approximately 13.1%.

At the user's request, the policy was changed to `q=0.8`, shape 1, tolerance 0.2.
This is a deliberate relaxation, not merely a computational approximation:

- The reference first-turn death probability is 20%; its allowed band is 0–40%.
- The reference conditional two-turn point probability is 16%; its band is 0–36%.
- The tolerance is **20 percentage points**, not 20% relative error.
- These bounds impose no positive minimum death rate; they function mainly as
  upper risk caps for this short adventure.

Those constants were frozen before validation with seed 20261102. The held-out
run took 12.362 seconds on the development machine, used 979,266 trajectories,
and had no censored or invalid runs. It collected exactly 160,000 observations
per row:

| Constraint | Deaths | Qualifying observations | Frequency |
|---|---:|---:|---:|
| First turn | 0 | 160000 | 0% |
| Death at 2, active at 0 | 0 | 160000 | 0% |
| Death at 3, active at 1 | 1374 | 160000 | 0.85875% |
| Death at 4, active at 2 | 16060 | 160000 | 10.0375% |
| Death at 5, active at 3 | 43753 | 160000 | 27.345625% |
| Death at 6, active at 4 | 22175 | 160000 | 13.859375% |
| Death at 7, active at 5 | 0 | 160000 | 0% |

All rational acceptance checks passed. The player rules and combat mechanics
were not changed to obtain this result.

## Runtime safeguards

`make validate` reproduces the fixed experiment. `make run` reruns that same
protocol on the current source before admitting Lighthouse to the menu.
`StatisticalAdventure.provenance` binds its counts to `validateCounts candidate`;
counts from another ruleset or story cannot be substituted as evidence.
The gameplay `--seed` option does not change the validation seed.

For each conditional row, only the first 160,000 trajectories active at that
turn contribute. Sampling does not stop based on observed death rates. Any
combat timeout or invalid trajectory aborts validation. Failure to fill every
row within two million trajectories also prevents admission. Aborting is not
conditioning the theorem on success: aborted executions issue no certificate.
They can only reduce the event of false approval under the reference model.

Replaying the same seed is reproducibility, not additional independent evidence.
After tuning rules, story, or policy against validation results, use a fresh
precommitted held-out validation experiment. Do not search for favorable seeds
or repeatedly tune on this holdout while retaining the original confidence claim.

## Exploratory diagnostics

`make audit` is separate from validation. It uses a much smaller fixed-size
sample and nominal simultaneous Hoeffding intervals, includes unresolved
probability from censored games, and reports capped lifetime estimates.
[The standard concentration bound](https://ai.stanford.edu/~gwthomas/notes/concentration.html)
is used only for diagnostics, not as the Lean proof of fairness. None of those
Float intervals can construct a statistical or exact admission certificate.
