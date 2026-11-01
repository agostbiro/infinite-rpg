# Exact binomial fairness intervals

`Rpg.Probability.StatisticalCandidate.fair` is the main theorem, specialized as
`Rpg.Lighthouse.fair` and `Rpg.Harbor.fair`.

## Protocol

- Run **1,000 games total**, fixed before validation.
- Use **90% confidence**: `confidenceDelta = 1/10`.
- First-turn death is row zero. For each `0 <= t < horizon`, another row measures
  `P(death exactly at t+2 | game active at t)`.
- Use each row's actual qualifying count. Do not continue sampling until an
  interval passes or reaches a chosen width.
- Admit the adventure only when every complete interval fits its Weibull band.

The constants are `validationGames` and `validationSeed` in
`Rpg/Probability/StatisticalAdmission.lean`, and `confidenceDelta` in
`Rpg/Probability/Confidence.lean`. The frozen seed is 20261103. Lighthouse uses
horizon 6; Harbor uses horizon 1. There is no claim beyond the selected window.

## What Lean proves

For an observed `k` deaths among `n` qualifying games, the Clopper–Pearson interval
contains probabilities `p` satisfying both exact binomial tail inequalities:

```
P_p(K <= k) >= delta/2
P_p(K >= k) >= delta/2
```

`binomial_coverage` proves that the true probability is excluded with probability
at most `delta`. The proof bounds each tail's rejection probability and combines
them; it does not assume a concentration inequality or a normal approximation.

The endpoints need not be rational. Eight bisection steps produce a conservative
rational enclosure on a 1/256 grid. Tail evaluations use exact integer arithmetic,
and `exactExpectation_correct` proves they equal the independent-Bernoulli model.
`confidenceInterval_encloses` proves that outward rounding cannot reduce coverage.
For zero observations the interval is `[0,1]`, and admission fails.

`fair` proves:

1. Each reported interval covers its true conditional expectation with probability
   at least 90%, including when its qualifying count is random.
2. Accepting the entire finite window while any true expectation violates its
   Weibull band has probability at most 10%.

These are per-interval coverage and a bound on false acceptance of the whole
check, not simultaneous coverage of every interval or a posterior probability
that an accepted adventure is fair. Rows may depend on one another.

## Accepted sampling assumptions

`BinomialSampling` states that, conditional on a row's qualifying count `n`, its
death count is binomial with that row's graph-derived probability. The theorem
averages over the distribution of `n`; no fixed denominator is assumed.
The joint observation law and sample-size laws are valid probability laws, and
the true probabilities lie in `[0,1]`.

Independent ideal trajectories and correspondence of the seeded simulator to this
model remain accepted assumptions. SplitMix64 and modulo-based choices are not
proved IID. No coverage theorem is assumed. The Lean proofs use only standard
axioms, with no `sorry`, new axioms, or `native_decide`.

## Admission and validation

`StatisticalAdventure` carries `fair`, source-bound counts, and passing interval
checks. Its provenance requires `counts = validateCounts candidate`; observations
from a different story, hero, ruleset, or horizon cannot be substituted.
`intervals_fit` proves that admitted intervals lie inside the shared policy bands.

Invalid trajectories or unresolved combat inside the tested window abort admission.
Continuing beyond the window is allowed. Zero qualifying observations cannot pass.
A failed batch is not retried until it passes; a changed protocol or tuning against
validation data needs a fresh precommitted experiment.

The 1,000-game Lighthouse run passed with these observations and rational interval
enclosures, using the unchanged policy `q=4/5`, shape `1`, tolerance `1/5`:

| Row | Deaths / qualifying games | Interval |
|---|---:|---:|
| First turn | 0 / 1000 | [0, 1/256] |
| Death at 2, active at 0 | 0 / 1000 | [0, 1/256] |
| Death at 3, active at 1 | 0 / 1000 | [0, 1/256] |
| Death at 4, active at 2 | 40 / 1000 | [7/256, 7/128] |
| Death at 5, active at 3 | 95 / 967 | [21/256, 15/128] |
| Death at 6, active at 4 | 33 / 679 | [9/256, 17/256] |
| Death at 7, active at 5 | 0 / 177 | [0, 5/256] |

`make validate` reproduces the batch and prints the intervals. `make run` checks
both adventures before play. Replaying a fixed seed is reproducibility, not new
independent evidence.

The mechanic skill runs its compiled screen and final admission with a shared
one-minute deadline. Builds do not rerun this held-out experiment; the final
command checks current source-bound counts, rather than comparing them with this
historical table. The fairness parameters and the theorem are unchanged.
