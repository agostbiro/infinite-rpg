import Rpg.Adventures.Lighthouse.Confidence

open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- Run the balance check on the Lighthouse with the fixed validation seed, and print each row. -/
def main : IO UInt32 := do
  IO.println "LIGHTHOUSE: EXACT BINOMIAL BALANCE CHECK"
  IO.println s!"Policy: q={weibullRetention}, shape={weibullShape}, tolerance={balanceTolerance}"
  IO.println s!"Window: first-turn death and death at t+2 for t < {Lighthouse.balanceHorizon}"
  IO.println s!"Fixed game batch: {validationGames}; interval failure bound={confidenceDelta}"
  IO.println s!"Validation seed={validationSeed}; round limit={validationRoundLimit}"
  IO.println "Coverage is proved under the accepted binomial sampling model, conditional on each row’s actual qualifying count."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let (counts, accepted) := admitStatistically Lighthouse.statisticalCandidate
  IO.println s!"elapsed-ms={(← IO.monoMsNow)-start}; games={counts.games}; aborted={counts.aborted}"
  for row in [:counts.trials.size] do
    let n := counts.trials[row]!
    let k := counts.deaths[row]!
    let interval := confidenceInterval confidenceDelta n k
    let target := if row = 0 then 1 - defaultPolicy.survival 1 else defaultPolicy.deathAtTwo (row-1)
    IO.println s!"row {row}: {k}/{n}; interval=[{interval.lower}, {interval.upper}]; Weibull target={target}"
  if accepted.isSome then
    IO.println "ACCEPTED: every exact-binomial interval enclosure fits the Weibull policy."
    IO.println "The theorem `balanced` gives per-row interval coverage and at most 10% false acceptance for this finite window under the sampling model."
    return 0
  IO.println "NOT ADMITTED: an interval failed, sampling was incomplete, or an outcome inside the window was unresolved."
  return 1
