import Rpg.Adventures.Lafayette.Confidence

open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- A rate as a percentage with two decimals, such as "11.13%". -/
def percent (r : Rat) : String :=
  let hundredths := (r * 10000).floor
  let rest := toString (100 + hundredths % 100) |>.drop 1
  s!"{hundredths / 100}.{rest}%"

/-- Print the balance curve and the target of each row. -/
def printPolicy (p : BalancePolicy) : IO Unit := do
  let rows := (List.finRange (Lafayette.balanceHorizon + 1)).map fun i =>
    percent (confidenceBandsFor p Lafayette.balanceHorizon i).target
  IO.println s!"Policy: q={p.retention}, shape={p.shape}, tolerance={p.tolerance}; alive after 10 turns={percent (p.survival 10)}; row targets={rows}"

/-- Read `--seed N` from the command line, or else use the fixed validation seed. -/
def seedArg : List String → Nat
  | "--seed" :: v :: _ => v.toNat?.getD validationSeed
  | _ :: rest => seedArg rest
  | [] => validationSeed

/-- Run the balance check on the built-in Adventure (Lafayette at Barren Hill), and print each row.
It uses the fixed validation seed, or the seed after `--seed`. -/
def main (args : List String) : IO UInt32 := do
  let seed := seedArg args
  IO.println "BUILT-IN ADVENTURE (LAFAYETTE AT BARREN HILL): EXACT BINOMIAL BALANCE CHECK"
  let policy := Lafayette.statisticalCandidate.policy
  printPolicy policy
  IO.println s!"Window: first-turn death and death at t+2 for t < {Lafayette.balanceHorizon}"
  IO.println s!"Fixed game batch: {validationGames}; interval failure bound={confidenceDelta}"
  IO.println s!"Validation seed={seed}; round limit={validationRoundLimit}"
  IO.println "Coverage is proved under the accepted binomial sampling model, conditional on each row’s actual qualifying count."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let (counts, accepted) := admitWithSeed Lafayette.statisticalCandidate seed
  IO.println s!"elapsed-ms={(← IO.monoMsNow)-start}; games={counts.games}; aborted={counts.aborted}"
  for row in [:counts.trials.size] do
    let n := counts.trials[row]!
    let k := counts.deaths[row]!
    let interval := confidenceInterval confidenceDelta n k
    let target := if row = 0 then 1 - policy.survival 1 else policy.deathAtTwo (row-1)
    IO.println s!"row {row}: {k}/{n}; interval=[{interval.lower}, {interval.upper}]; Weibull target={target}"
  if accepted.isSome then
    IO.println "ACCEPTED: all intervals fit the policy, and short loops are absent. The combat check is separate: make certify."
    IO.println s!"The theorem `balanced` gives per-row interval coverage and at most {100 * confidenceDelta}% false acceptance for this finite window under the sampling model."
    return 0
  IO.println "NOT ADMITTED: balance, sampling, or short-loop checks failed."
  for error in failedRows Lafayette.balanceHorizon counts confidenceDelta 0 policy do
    IO.println error
  return 1
