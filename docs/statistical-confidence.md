# Finite fairness confidence

## The main theorem: `fair`

`Rpg/Probability/StatisticalAdmission.lean` defines `Fair candidate` and proves
`StatisticalCandidate.fair`. Adventures specialize it as `Rpg.Lighthouse.fair`
and `Rpg.Harbor.fair`. This is the shared finite statistical guarantee used for
admission.

An adventure selects a positive `horizon = H` before validation. Row zero checks
first-turn death. Rows `t+1`, for `0 <= t < H`, estimate

```
p_t = E[1{death at t+2} | game active at t]
    = P(death exactly at t+2 | game active at t).
```

Their Weibull targets are `(S(t+1) - S(t+2)) / S(t)`, where
`S(t) = q^(t^shape)`. The first-turn target is `1 - S(1)`.
Lighthouse uses `H = 6`, so its conditional rows cover deaths at turns 2 through
7. Harbor uses `H = 1`. No claim is made about later times.

For `k` deaths among `n` qualifying observations, the exact rational interval is

```
[max(0, k/n - epsilon), min(1, k/n + epsilon)].
```

The theorem `fair` proves two conclusions under the sampling model:

1. For each row, the probability that its interval misses the true conditional
   expectation is at most `delta`.
2. The probability of accepting every row when any true expectation lies outside
   its Weibull tolerance band is at most `delta`.

The first statement is per-row coverage, not simultaneous coverage of all
intervals. The second is a guarantee for the whole finite admission decision:
if any fixed row violates its band, approving all rows requires falsely approving
that row. Independence between rows is unnecessary.

Admission requires the **whole interval** to fit inside the target's tolerance
band. `StatisticalAdventure.intervals_fit` proves that the executable rational
checks enforce this containment. The `fair` theorem is a guarantee for the
validation procedure; a candidate also needs passing source-bound observations
to become playable.

## Statistical proof and accepted model

`Rpg/Probability/Confidence.lean` defines exact binomial expectations from
independent Bernoulli trials. It proves their moments, the variance bound
`p*(1-p) <= 1/4`, and the confidence bound used above. No statistical inequality
is assumed. The required arithmetic budget is

```
n / 4 <= delta * (n * epsilon)^2.
```

The editable protocol constants are:

- `confidenceSamples = 160000` qualifying observations per row.
- `confidenceEpsilon = 1/25` (four percentage points).
- `confidenceDelta = 1/1000` (0.1% failure probability).

`confidenceBudget` proves the budget using exact arithmetic. The confidence and
fairness proofs use only standard Lean axioms, with no `sorry`, new axioms, or
`native_decide`.

The accepted sampling model consists of a valid joint observation law, true
probabilities in `[0,1]`, and binomial row marginals with those graph-derived
probabilities. It models independent ideal trajectories and the first fixed
number of qualifying observations; rows can share trajectories. Correspondence
between the seeded executable sampler and that ideal model is assumed, including
the idealization of PRNG and modulo-based choices. SplitMix64 is not proved IID.
There are no additional graph-normalization, active-start, or tail hypotheses
in `fair`.

The error bound concerns repeated experiments under that model. It is not a
Bayesian probability that this particular adventure is fair after observing its
counts.

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

## Admission and finite observation window

Both adventures use the same `admitStatistically` gate. A playable
`StatisticalAdventure` carries the `fair` theorem, source-bound counts, and a
proof that every numerical check passed. Its `provenance` equality requires
`counts = validateCounts candidate`; a different story, ruleset, hero, or window
cannot supply the evidence.

`make validate` prints Lighthouse's rational intervals and Weibull targets.
`make run` checks both adventures before showing them in the menu. Gameplay
`--seed` does not change the validation seed.

Only the first 160,000 qualifying trajectories contribute to each row. Sampling
does not stop based on death rates. The largest tested death turn is `H+1`, so
trajectories are observed only through that turn. An unresolved combat outcome
inside that window aborts validation; continued play beyond the window is allowed.
Invalid trajectories or failure to fill every row within two million games also
prevent admission. A conditioning event that never occurs cannot fill its row
and therefore cannot pass. No termination or decreasing-rank proof is required.

Replaying the same seed is reproducibility, not new independent evidence. The
finite refactor preserves Lighthouse's window, policy, sample size, and recorded
counts. After tuning those inputs using validation results, choose a fresh
precommitted held-out experiment; do not search for favorable seeds.

## Exploratory diagnostics

`make audit` remains separate from admission. It reports floating-point estimates
and capped lifetime intervals using an exploratory concentration calculation.
Those intervals do not supply the `fair` theorem or admission evidence.
