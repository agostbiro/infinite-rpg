import Rpg.Adventures.TestAdventure.Confidence

open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- A rate as a percentage with two decimals, such as "11.13%". -/
def percent (r : Rat) : String :=
  let hundredths := (r * 10000).floor
  let rest := toString (100 + hundredths % 100) |>.drop 1
  s!"{hundredths / 100}.{rest}%"

/-- Print the balance curve and the target of each row. -/
def printPolicy (p : BalancePolicy) : IO Unit := do
  let rows := (List.finRange (TestAdventure.balanceHorizon + 1)).map fun i =>
    percent (confidenceBandsFor p TestAdventure.balanceHorizon i).target
  IO.println s!"Policy: q={p.retention}, shape={p.shape}, tolerance={p.tolerance}; alive after 10 turns={percent (p.survival 10)}; row targets={rows}"

/-- Run the balance check on the test Adventure with the fixed validation seed, and print each row. -/
def main : IO UInt32 := do
  IO.println "TEST ADVENTURE (THE BANDIT CAMP): EXACT BINOMIAL BALANCE CHECK"
  let policy := TestAdventure.statisticalCandidate.policy
  printPolicy policy
  IO.println s!"Window: first-turn death and death at t+2 for t < {TestAdventure.balanceHorizon}"
  IO.println s!"Fixed game batch: {validationGames}; interval failure bound={confidenceDelta}"
  IO.println s!"Validation seed={validationSeed}; round limit={validationRoundLimit}"
  IO.println "Coverage is proved under the accepted binomial sampling model, conditional on each row’s actual qualifying count."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let (counts, accepted) := admitStatistically TestAdventure.statisticalCandidate
  IO.println s!"elapsed-ms={(← IO.monoMsNow)-start}; games={counts.games}; aborted={counts.aborted}"
  for row in [:counts.trials.size] do
    let n := counts.trials[row]!
    let k := counts.deaths[row]!
    let interval := confidenceInterval confidenceDelta n k
    let target := if row = 0 then 1 - policy.survival 1 else policy.deathAtTwo (row-1)
    IO.println s!"row {row}: {k}/{n}; interval=[{interval.lower}, {interval.upper}]; Weibull target={target}"
  if accepted.isSome then
    IO.println "ACCEPTED: every exact-binomial interval enclosure fits the Weibull policy."
    IO.println s!"The theorem `balanced` gives per-row interval coverage and at most {100 * confidenceDelta}% false acceptance for this finite window under the sampling model."
    return 0
  IO.println "NOT ADMITTED: an interval failed, sampling was incomplete, or an outcome inside the window was unresolved."
  return 1
