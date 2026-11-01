# Exact binomial balance intervals

`Rpg.Probability.StatisticalCandidate.balanced` is the main theorem, specialized as
`Rpg.TestAdventure.balanced`. It is a theorem about the test, true for every candidate.
What admits an Adventure is the run-time check `admitStatistically` (fixed seed) or
`admitWithSeed` (a Wish, with a fresh seed).

## Protocol

- Run **1,200 games total** (`difficultyGames`), fixed before validation.
- Use **95% confidence**: `confidenceDelta = 1/20`.
- First-turn death is row zero. For each `0 <= t < horizon`, another row measures
  `P(death exactly at t+2 | game active at t)`.
- Use each row's actual qualifying count. Do not continue sampling until an
  interval passes or reaches a chosen width.
- Admit the adventure only when every complete interval fits the Weibull band of its own
  policy: the curve of its difficulty level, with a tolerance of 5 points.

The constants are `difficultyGames` and `validationSeed` in
`Rpg/Probability/StatisticalAdmission.lean`, and `confidenceDelta` in
`Rpg/Probability/Confidence.lean`. The frozen seed is 20261103. The test Adventure and every Wish use
horizon 5. There is no claim beyond the selected window. The first row with a band whose lower
edge is above 0 is row 4 on easy, row 2 on medium, and row 1 on hard. So a candidate needs at
least that horizon before the check can reject an Adventure where the Character never dies
(`TestStory.lean` shows this for medium).

## Difficulty levels

The Player picks easy, medium, or hard for a Wish. Each level is a `BalancePolicy`
(`DifficultyLevel.policy` in `Rpg/Probability/Weibull.lean`): shape 2, a tolerance of 5 points
(`difficultyTolerance`), and a q that leaves 50%, 30%, or 10% of Characters alive after
10 turns. The targets of the rows, from first-turn death to death at 6 given active at 4, are:

| Level | q | Row targets |
|---|---:|---|
| easy | 993092495/10^9 | 0.69%, 2.04%, 3.33%, 4.57%, 5.76%, 6.89% |
| medium | 988032459/10^9 | 1.19%, 3.50%, 5.63%, 7.61%, 9.43%, 11.13% |
| hard | 977237220/10^9 | 2.27%, 6.52%, 10.14%, 13.26%, 15.93%, 18.18% |

`StatisticalCandidate.policy` holds the policy of a candidate; with no explicit policy it is
medium. A `Game` holds the policy of its Adventure, and a live change is checked against that
policy and keeps it (`WorldChange.Prepared.keeps_policy`). The test Adventure fails the medium
curve, so it is exempt: it keeps `defaultPolicy` (q = 19/20, tolerance 1/5) until a new default
Adventure that passes medium takes its place (item 1 in [follow-ups](follow-ups.md)).
`defaultPolicy` and `balanceTolerance` stay as they were; no level uses them.

At 1,200 games, an Adventure that sits on its curve passes the 5-point tolerance even when its
counts are 2 standard deviations off. The last row is always the limit, because it has the
fewest qualifying games.

A Wish gets up to 3 tries, each with a fresh random seed that is saved with the
Adventure. If the sampling assumptions hold conditional on the history of each try,
a union bound gives at most 3 × 5% = 15% false acceptance over the 3 tries.
Lean proves the per-try bound; it does not prove this retry bound.

In-game rule changes use a separate, rigorously proved retry protocol. Validation attempt
`n` spends `confidenceDelta / 2^(n+1)`, starting with 97.5% intervals. `RetryTree.balanced`
bounds false acceptance across any finite adaptive sequence by the overall 5% budget,
assuming the sampling model at every history. Screening does not spend that budget;
each frozen proposal uses a fresh validation batch of 1,200 games from the updated adventure beginning, including combat, against the policy of the game it changes.
See [live rule changes](live-rule-changes.md) for admission scope and checkpoint preservation.

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

`balanced` proves:

1. Each reported interval covers its true conditional expectation with probability
   at least 95%, including when its qualifying count is random.
2. Accepting the entire finite window while any true expectation violates its
   Weibull band has probability at most 5%.

These are per-interval coverage and a bound on false acceptance of the whole
check, not simultaneous coverage of every interval or a posterior probability
that an accepted adventure is balanced. Rows may depend on one another.

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

`StatisticalAdventure` carries `balanced`, source-bound counts, and passing interval
checks. Its provenance requires `counts = sampleCounts candidate seed difficultyGames`, with the seed it records; observations
from a different story, hero, ruleset, or horizon cannot be substituted.
`intervals_fit` proves that admitted intervals lie inside the bands of the candidate's own policy.

Invalid trajectories or unresolved combat inside the tested window abort admission.
Continuing beyond the window is allowed. Zero qualifying observations cannot pass.
A failed batch is not retried until it passes; a changed protocol or tuning against
validation data needs a fresh precommitted experiment.

The rest of this section and the next one are history: they describe the 1,000-game check
with `defaultPolicy`, before the difficulty levels.

The policy changed in the merge with the browser game (ADR 0004): Mara has a broadsword
again, the model's Player picks maneuvers at random, and the curve is shape 2, q = 19/20,
tolerance 1/5, horizon 5. The values were picked on the screening seed (1). Then the fixed
seed was run once on the earlier built-in Adventure (removed since). Its graph is now the test
Adventure, The Bandit Camp. The same 1,000-game batch was replayed after changing to
95% confidence and still passed, with unchanged observations and these interval enclosures:

| Row | Deaths / qualifying games | Interval | Band |
|---|---:|---:|---:|
| First turn | 0 / 1000 | [0, 1/256] | [0, 25.0%] |
| Death at 2, active at 0 | 0 / 1000 | [0, 1/256] | [0, 33.5%] |
| Death at 3, active at 1 | 22 / 1000 | [3/256, 9/256] | [0, 39.4%] |
| Death at 4, active at 2 | 148 / 1000 | [1/8, 11/64] | [3.3%, 43.3%] |
| Death at 5, active at 3 | 346 / 946 | [85/256, 51/128] | [5.8%, 45.8%] |
| Death at 6, active at 4 | 130 / 666 | [21/128, 59/256] | [7.2%, 47.2%] |

`make validate` now runs 1,200 games, so its counts differ from this table. Replaying a fixed seed is reproducibility, not new
independent evidence.

The mechanic skill runs its compiled screen and final admission with a shared
one-minute deadline. Builds do not rerun this held-out experiment; the final
command checks current source-bound counts, rather than comparing them with this
historical table. The skill uses the shared balance parameters and theorem.

## Shared-tactics expansion and frozen validation

The shared meta rules and the expanded earlier built-in Adventure (now the test Adventure) were
designed using screening seed 1. The
production policy remains q=19/20, shape=2, tolerance=1/5, confidence=95%, horizon=5, with
1,000 games and the 200-round fight limit. One final validation of the frozen gameplay
change on seed 20261103 passed with the following observations:

| Row | Deaths / qualifying games | Exact rational interval enclosure |
|---|---:|---:|
| First turn | 0 / 1000 | [0, 1/256] |
| Death at 2, active at 0 | 0 / 1000 | [0, 1/256] |
| Death at 3, active at 1 | 69 / 1000 | [13/256, 23/256] |
| Death at 4, active at 2 | 143 / 1000 | [31/256, 43/256] |
| Death at 5, active at 3 | 312 / 910 | [79/256, 3/8] |
| Death at 6, active at 4 | 149 / 642 | [51/256, 69/256] |

The final runner completed in 16.41 seconds. A later audit after adding scope proofs passed
for 854 project theorems. Linux-only kernel replay and Comparator remain pending.

`StatisticalCandidate.balancedAt` takes an optional explicit policy, whose default is the
candidate's own policy. `ValidationAccepted` and `failedRows` take the policy as an explicit
argument with no default, so each caller names the curve that it checks against.
The same theorem therefore supports the experimental comparisons without assuming new
coverage bounds. The study reads validated parameters from `experiments/plan.json`; none
of its results authorizes game installation or changes the shipped settings.

The [study report](../experiments/results/report.html) compares seven legal game variants
using 140,000 lifetime trajectories and 35,000 separate admission trajectories. It varies
q, shape, tolerance, and confidence while retaining the same 1,000-game batch size. The
conditional means describe deaths actually observed; a winning character is not assigned
a fictitious death time. All runs completed within the recorded caps, with zero invalid
or censored trajectories. These are exploratory observations under the accepted simulator
assumptions, not an all-time guarantee or simultaneous confidence statement.
