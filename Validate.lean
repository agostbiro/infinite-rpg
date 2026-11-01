import Rpg.Adventures.Lighthouse.Confidence

open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- Run the frozen held-out statistical validation protocol on current Lighthouse inputs. -/
def main : IO UInt32 := do
  IO.println "LIGHTHOUSE: LEAN-PROVED STATISTICAL CONFIDENCE PROTOCOL"
  IO.println s!"Policy: q={weibullRetention}, shape={weibullShape}, tolerance={fairnessTolerance}"
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
    IO.println s!"row {row}: {k}/{n}, frequency={k.toFloat / n.toFloat}"
  if accepted.isSome then
    IO.println "ACCEPTED: every rational confidence interval fits the frozen policy."
    IO.println "This is a statistical admission under a proved risk bound, not an exact isFair proof."
    return 0
  IO.println "NOT ADMITTED: an interval failed, sampling was incomplete, or a trajectory was censored."
  return 1
