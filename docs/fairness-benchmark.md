# Fairness benchmark: 5,000 games through ten choices

Measured on 2026-11-01, macOS arm64, Lean 4.35.0, native optimized executable.
The final requested configuration is **5,000 games per difficulty and ten choices**.
This limits the statistical claim; it does not shorten the playable campaign.

## Protocol

- Use the three frozen Napoleon candidates previously balanced under v1. Apply the new v2 targets without changing their graph or encounters.
- Start every game at the initial state. Use the real simulator's uniform choices, maneuvers and targets. A choice includes its whole fight.
- Check first-choice death, nine conditional windows `P(t < T <= t+2 | T > t)` for `t = 0..8`, and cumulative death by choice ten: **11 comparisons**.
- Retain Weibull shape 2, 95% exact binomial intervals, and ±5 percentage point bands. Each entire conservative interval must fit its band.
- Compute every interval, even when an earlier row fails. Include JSON parsing, graph legality, noSmallCycles checks, simulation, confidence calculations and a checked coverage replay in the full internal timing.
- Reuse the three recorded seeds. This is a reproducible diagnostic, not a new independent acceptance certificate. No candidate or seed was selected to obtain a passing result.

The source snapshots, hashes, seeds, exact intervals and timings are in
[the machine-readable report](reports/fairness-5000-ten.json).

## Time for each complete batch

Seconds, one sequential batch per difficulty; no extrapolation to other machines.

| Difficulty | Graph checks | 5,000 simulations | All 11 intervals | Coverage replay | Internal total | Whole process |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Easy | 0.676 | 0.042 | 0.448 | 0.086 | **1.252** | **3.209** |
| Medium | 0.699 | 0.033 | 0.596 | 0.067 | **1.394** | **1.412** |
| Hard | 0.692 | 0.026 | 0.681 | 0.054 | **1.453** | **1.470** |

Whole-process time includes executable startup and final output. The first launch
had about 1.96 seconds outside the measured engine work; later launches had about
0.02 seconds. Builds and Claude adventure/environment generation are excluded.
The three complete processes took **6.09 seconds** for 15,000 sampled games.

The internal batch costs average 0.250, 0.279 and 0.291 milliseconds per game,
including all calculations and checks. Their equivalent rates are about 240,000,
215,000 and 206,000 games/minute. These are batch-derived rates, not measured
one-minute runs; startup affects short invocations.

## Fairness results

| Difficulty | Target death by ten | Observed | Conservative 95% interval | Ten-choice row | All 11 rows |
| --- | ---: | ---: | --- | --- | --- |
| Easy | 50% | 51.58% | [50.00%, 53.13%] | Pass | 7 pass, 4 inconclusive |
| Medium | 70% | 70.40% | [68.75%, 71.88%] | Pass | 5 pass, 4 outside, 2 inconclusive |
| Hard | 90% | 81.54% | [80.08%, 82.81%] | Outside | 3 pass, 7 outside, 1 inconclusive |

**None of the current candidates passes all criteria.** Easy is not admitted because
four intervals cross a band boundary. Medium and Hard also have intervals wholly
outside their bands. The ±5-point band and 95% confidence have not been relaxed.
These are old candidates under a stronger test, not newly balanced v2 games.

All **17 graph nodes structurally reachable within ten choices** were visited in
each batch. The campaign has 117 nodes; later nodes are outside this experiment.
Visiting a node does not establish a precise local risk estimate for every HP state.
The test estimates the global survival-conditioned mixture under the uniform player;
it does not force visits to rare nodes or certify every node separately.

## Why it is faster

Lean already compiles the engine to C. The bottleneck was recomputing binomial tails
by repeatedly blending a whole count table: roughly `n * (k+1)` integer operations
for a tail with `n` trials and threshold `k`.

The new evaluator walks the count table once using consecutive binomial weights:

`w_0 = (b-a)^n`

`w_(j+1) = w_j * (n-j)/(j+1) * a/(b-a)`

It sums the weights before dividing by `b^n`. Arithmetic stays exact. The endpoint
`a = b` uses the original evaluator. Large-integer operation costs still depend on
integer size; “linear” counts recurrence steps, not bit complexity.

The kernel checks the function equalities `Fast.exactExpectation_eq_fast`,
`Fast.lowerTail_eq_fast` and `Fast.upperTail_eq_fast`. Lean's `csimp` compiler rule
uses these proved replacements. No imported C computation, floating-point tail
approximation, additional axiom, or altered statistical specification is involved.

For a like-for-like comparison, the earlier **5,000-game, fifteen-choice** Hard batch
(seed 71001, all 16 intervals) took **357.665 seconds before** and **1.371 seconds
after**: approximately **261 times faster overall**. Interval calculation alone fell
from 357.005 to 0.724 seconds. All sixteen count/interval/status results match exactly.
The ten-choice timings above use the user's subsequently reduced horizon.

The previously requested 10,000-game, fifteen-choice experiment had already
completed before the scope changed. Its unchanged historical results are retained
in [the separate report](reports/fairness-10000.json); they are not the production budget.

## Checks and reproduction

- All 33 current interval endpoints match an independent exact-integer implementation.
- All 16 original baseline intervals match the optimized native Lean executable.
- Small count tables, endpoint probabilities and signed statistics match the original evaluator.
- Coverage recording matches the production trace and RNG state for every game, then reconstructs the same observation counts.
- Lean builds and theorem axiom audits pass with only `propext`, `Classical.choice` and `Quot.sound`. Comparator's separate sandbox is Linux-only and could not run on this macOS host; that final gate remains outstanding.

From the repository root:

```sh
lake build Rpg rpg inspect-adventure benchmark-fairness Comparator.Proofs
python3 scripts/benchmark_fairness.py --output work/fairness-replay.json
```

The replay checks source hashes, all recorded counts, interval endpoints, statuses
and coverage. It preserves the original measurement report and writes new timings
to the requested file. The verified replay matched all counts, intervals, statuses and coverage; its whole-process times were 1.365, 1.404 and 1.453 seconds. Replaying seeds supplies no new independent statistical evidence.
The production validation budget remains 5,000. Existing running game servers were
not restarted; the new settings apply when the rebuilt server is next launched.
