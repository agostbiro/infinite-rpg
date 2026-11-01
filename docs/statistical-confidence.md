# Weibull windows and statistical admission

## Reference curve

Let `T` be the choice at which the uniform test player dies. A successful ending has `T = infinity`. One choice includes its entire fight; walking and waiting do not advance this clock.

For the selected probability `b` of death by choice ten, keep Weibull shape `k = 2` and choose only its scale:

`lambda = 10 / sqrt(-ln(1-b))`

`S_b(t) = P(T > t) = exp(-(t/lambda)^2) = (1-b)^((t/10)^2)`

| Difficulty | Death by ten b | Survival at ten | Scale lambda |
| --- | ---: | ---: | ---: |
| Easy | 50% | 50% | 12.011224 |
| Medium | 70% | 30% | 9.113636 |
| Hard | 90% | 10% | 6.590102 |

The conditional expectation is of an indicator, not of the death time:

`q_t = E[1{t < T <= t+2} | T > t] = P(t < T <= t+2 | T > t)`

Its reference target is `w_b(t) = 1 - S_b(t+2)/S_b(t) = 1 - (1-b)^((4t+4)/100)`.
Survival decreases and these two-choice risks increase. Lean uses exact rational retention parameters approximating `(1-b)^(1/100)`; `difficulty_target` bounds the ten-choice approximation error below one millionth.

## Conditional risks imply the ten-choice target

The chain rule gives:

`P(T > 10) = product(j = 0..4) (1 - q_(2j))`.

Consequently, exact equality `q_t = w_b(t)` gives `P(T <= 10) = b`.
`conditional_windows_at_ten` proves the survival-ratio identity in Lean, and
`difficulty_windows_at_ten` checks it for all three actual rational curves.
An error of at most five percentage points in each conditional risk does **not**
imply an error of at most five points at ten; the product accumulates errors.
The admission test therefore also checks death by ten directly.

## Protocol for new Wishes (difficulty-*-v2)

- Fix the candidate before drawing its final validation seed.
- Run **5,000 trajectories through the first ten choices**, fixed in advance. Do not search for a passing seed or increase the batch until it passes.
- Use exact binomial **95% confidence** intervals and an absolute **±0.05** target band.
- Test first-choice death, the 9 conditional windows `t = 0..8` (through choice 10), and death by choice ten: **11 comparisons**.
- Count death at either `t+1` or `t+2` in each conditional window. Include successful endings among survivors, with zero subsequent deaths.
- Use each row's actual survivor count. Overlapping window counts must not be summed to estimate cumulative death.
- Admit only if every entire interval fits its band. An interval that overlaps a band edge is **inconclusive**; an interval wholly outside is reported as **outside-band**. Both prevent admission.
- Invalid or unresolved in-window trajectories abort validation. Empty observations cannot pass.

The ten-choice window is the requested statistical scope, not a campaign length limit. Under the Hard reference, about 1,145 of 5,000 games survive through choice 8, the last conditioning time. Near a band boundary a result can still be inconclusive; no band or confidence level is relaxed to make it pass.

The server may use up to six authoring/training repairs. Training can adjust enemy parameters and request changes to encounter frequency or branches. The frozen candidate then receives **one independent final batch**. A failed final batch stops the Wish. Replaying a recorded seed is reproducibility, not new independent evidence. Repeated user retries do not inherit a single-test error guarantee.

## What Lean proves

The Clopper–Pearson interval inverts both exact binomial tails at `delta/2`.
Eight bisection steps enclose its endpoints conservatively on a 1/256 rational grid.
`binomial_coverage`, `exactExpectation_correct` and `confidenceInterval_encloses`
prove coverage and the exact arithmetic used by the test. No normal approximation is used.

For the new protocol, `StatisticalCandidate.fair` proves, under its sampling assumptions:

1. Each interval misses its true probability with risk at most 5%, including random survivor counts.
2. If any true tested probability violates its band, accepting the entire candidate has risk at most 5%.

These are per-interval coverage and a false-acceptance bound for the complete decision. They are not simultaneous coverage of all intervals, nor a posterior probability that an accepted game is fair. Rows may be dependent.

`StatisticalAdventure` records the candidate, policy, seed, actual sampled counts and proof of acceptance. `intervals_fit` proves the interval containment. `balanced` includes this source-bound acceptance in graph validity; `noSmallCycles` excludes cycles of one, two or three edges. See [the graph formalization](3d-formalization.md#10-theorem-balanced-validity-includes-balance).

## Sampling assumptions and rare nodes

`BinomialSampling` assumes that, conditional on a row's qualifying count, deaths have the binomial law with that row's graph-derived probability. Independent ideal trajectories and correspondence with the engine's seeded simulator remain assumptions. SplitMix64 and modulo choices are not proved IID. The Lean proofs add no axioms beyond the standard permitted set.

A rare node can be tested directly: start independent two-choice continuations from a fixed, reachable **complete state**, including HP, and estimate its local death probability. This avoids waiting for random full trajectories to reach it. It does not by itself estimate the aggregate `q_t` above. That aggregate also depends on the conditional distribution of states at time `t`.

Reusing one observed state for thousands of continuations measures that state's risk precisely; it does not give thousands of independent observations of the distribution of surviving states. Any weighted aggregation must also account for uncertainty in those weights. Cached states or weights must be invalidated when a changed rule affects their reachability or distribution. Direct rare-state admission is a proposed extension, not an implemented replacement for the global test.

## Implementation checks

The Lean build, endpoint and interval regression tests, and axiom audits passed.
`Fast.exactExpectation_eq_fast`, `Fast.lowerTail_eq_fast` and
`Fast.upperTail_eq_fast` prove that the linear evaluator equals the original exact
binomial calculation. Compiler simplification uses these equalities; no C foreign
function or floating-point approximation is added. Lean already compiles the engine
to C.

The current benchmark runs 5,000 games per difficulty through ten choices and
computes all eleven intervals, even after a failed row. See the
[measured results and reproducible commands](fairness-benchmark.md). The current
Napoleon candidates do not pass every band. Comparator's separate sandbox run
requires Linux and could not run on this macOS host. Active game servers were not
restarted by this change.

## Historical saves

`legacy`, `exploration-10-v1` and `difficulty-*-v1` retain their recorded protocol: 1,000 games, 90% intervals, tolerance 1/5, death **exactly** at `t+2` conditional on the game still running at `t`. Lighthouse uses horizon 5; exploration and v1 difficulties use horizon 14. They are not certificates for v2.

The earlier Napoleon and balanced-difficulty reports are historical results under these older policies. They do not establish the new ±5-point window criteria.

### Historical Lighthouse measurements

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

The mechanic skill runs its compiled screen and final admission with a shared
one-minute deadline. Builds do not rerun this held-out experiment; the final
command checks current source-bound counts, rather than comparing them with this
historical table. These measurements apply only to the historical default policy.
