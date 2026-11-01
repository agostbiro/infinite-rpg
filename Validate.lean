import Rpg.Adventures.Lighthouse.Confidence

open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- Run the frozen held-out statistical validation protocol on current Lighthouse inputs. -/
def main : IO UInt32 := do
  IO.println "LIGHTHOUSE: FINITE FAIRNESS CONFIDENCE PROTOCOL"
  IO.println s!"Policy: q={weibullRetention}, shape={weibullShape}, tolerance={fairnessTolerance}"
  IO.println s!"Window: first-turn death and death at t+2 for t < {Lighthouse.fairnessHorizon}"
  IO.println s!"Required observations per row: {confidenceSamples}; error radius={confidenceEpsilon}; false-acceptance bound={confidenceDelta}"
  IO.println s!"Held-out seed={validationSeed}; maximum games={validationMaxGames}; round limit={validationRoundLimit}"
  IO.println "The risk theorem assumes the stated independent Bernoulli sampling model. SplitMix64 is not proved IID."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let (counts, accepted) := admitStatistically Lighthouse.statisticalCandidate
  IO.println s!"elapsed-ms={(← IO.monoMsNow)-start}; games={counts.games}; aborted={counts.aborted}"
  for row in [:counts.trials.size] do
    let n := counts.trials[row]!
    let k := counts.deaths[row]!
    let interval := confidenceInterval confidenceEpsilon n k
    let target := if row = 0 then 1 - defaultPolicy.survival 1 else defaultPolicy.deathAtTwo (row-1)
    IO.println s!"row {row}: {k}/{n}; interval=[{interval.lower}, {interval.upper}]; Weibull target={target}"
  if accepted.isSome then
    IO.println "ACCEPTED: every rational confidence interval fits the frozen policy."
    IO.println "The fair theorem gives per-row interval coverage and at most 0.1% false acceptance for this finite window under the sampling model."
    return 0
  IO.println "NOT ADMITTED: an interval failed, sampling was incomplete, or an outcome inside the window was unresolved."
  return 1
