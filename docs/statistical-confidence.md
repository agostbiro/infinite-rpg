# Exact binomial fairness intervals

`Rpg.Probability.StatisticalCandidate.fair` is the main theorem, specialized as
`Rpg.Lighthouse.fair`. It is a theorem about the test, true for every candidate.
What admits an Adventure is the run-time check `admitStatistically` (fixed seed) or
`admitWithSeed` (a Wish, with a fresh seed).

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
`Rpg/Probability/Confidence.lean`. The frozen seed is 20261103. Lighthouse and every Wish use
horizon 5. There is no claim beyond the selected window. Only rows 3 and later have a band with a
lower edge above 0, so a candidate needs horizon 3 or more before the check can reject an
Adventure where the Character never dies (`TestStory.lean` shows this).

A Wish gets up to 3 tries, each with a fresh random seed that is saved with the
Adventure. Each try is a new test, so for a Wish the chance to accept an Adventure
that breaks a band is at most 3 × 10% = 30%.

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
checks. Its provenance requires `counts = sampleCounts candidate seed validationGames`, with the seed it records; observations
from a different story, hero, ruleset, or horizon cannot be substituted.
`intervals_fit` proves that admitted intervals lie inside the shared policy bands.

Invalid trajectories or unresolved combat inside the tested window abort admission.
Continuing beyond the window is allowed. Zero qualifying observations cannot pass.
A failed batch is not retried until it passes; a changed protocol or tuning against
validation data needs a fresh precommitted experiment.

The policy changed in the merge with the browser game (ADR 0004): Mara has a broadsword
again, the model's Player picks maneuvers at random, and the curve is shape 2, q = 19/20,
tolerance 1/5, horizon 5. The values were picked on the screening seed (1). Then the fixed
seed was run once, and the 1,000-game Lighthouse run passed with these observations and
rational interval enclosures:

| Row | Deaths / qualifying games | Interval | Band |
|---|---:|---:|---:|
| First turn | 0 / 1000 | [0, 1/256] | [0, 25.0%] |
| Death at 2, active at 0 | 0 / 1000 | [0, 1/256] | [0, 33.5%] |
| Death at 3, active at 1 | 22 / 1000 | [3/256, 9/256] | [0, 39.4%] |
| Death at 4, active at 2 | 148 / 1000 | [33/256, 43/256] | [3.3%, 43.3%] |
| Death at 5, active at 3 | 346 / 946 | [43/128, 101/256] | [5.8%, 45.8%] |
| Death at 6, active at 4 | 130 / 666 | [43/256, 57/256] | [7.2%, 47.2%] |

`make validate` reproduces the batch and prints the intervals. `make run` checks
the Lighthouse before play and stops if it fails. Replaying a fixed seed is reproducibility, not new
independent evidence.
