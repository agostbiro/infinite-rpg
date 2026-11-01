import Rpg.Catalog

/-!
Run the compiled exploratory screen, or source-bound admission after the mechanic
is frozen. Both modes use the same Lean parameters and return failure on any
rejected, empty, or incomplete row. Run: `lake exe screen [--validation]`.
-/
open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- Exploration uses a seed distinct from the precommitted validation seed. -/
def screenSeed : Nat := 1

#guard screenSeed != validationSeed

/-- Display a rational proportion as a percentage rounded down to two decimals. -/
def percent (r : Rat) : String :=
  let hundredths := r.num * 10000 / r.den
  let cents := hundredths % 100
  s!"{hundredths / 100}.{if cents < 10 then "0" else ""}{cents}%"

/-- Report every row and reject the entire candidate if any check fails. -/
def report (a : StatisticalCandidate) (validation : Bool) : IO Bool := do
  let (c, admitted) := if validation then
      let (counts, evidence) := admitStatistically a
      (counts, evidence.isSome)
    else (sampleCounts a screenSeed validationGames, true)
  IO.println s!"== {a.story.title} (horizon {a.horizon}, {c.games} games)"
  if c.aborted then
    IO.println "ABORTED: an outcome inside the window was unresolved or invalid."
    return false
  let mut passed := admitted && c.games == validationGames
  for row in [:a.horizon + 1] do
    let some i := (if h : row < a.horizon + 1 then some (⟨row, h⟩ : Fin (a.horizon + 1)) else none)
      | continue
    let count := c.observation row
    let name := if row = 0 then "death on turn 1" else s!"death on turn {row + 1} given active at turn {row - 1}"
    if count.trials = 0 then
      IO.println s!"{name}: NO DATA"
      passed := false
      continue
    let band := confidenceBands a.horizon i
    let interval := confidenceInterval confidenceDelta count.trials count.deaths
    let low := max 0 (band.target - band.tolerance)
    let high := min 1 (band.target + band.tolerance)
    let ok := decide (acceptsCount band confidenceDelta count)
    passed := passed && ok
    let bounds := if validation then s!"[{interval.lower}, {interval.upper}]"
      else s!"[{percent interval.lower}, {percent interval.upper}]"
    IO.println s!"{name}: {count.deaths}/{count.trials}, interval {bounds}, band [{percent low}, {percent high}]: {if ok then "ok" else "FAIL"}"
  if validation then
    IO.println (if passed then "ADMITTED" else "NOT ADMITTED")
  return passed

/-- The compiled entry point fails if any catalog adventure fails its selected check. -/
def main (args : List String) : IO UInt32 := do
  if args != [] && args != ["--validation"] then
    IO.eprintln "Usage: screen [--validation]"
    return 2
  let validation := args == ["--validation"]
  let label := if validation then "Validation" else "Screen"
  IO.println s!"{label}: {validationGames} games per adventure; round limit={validationRoundLimit}; interval failure bound={confidenceDelta}; endpoint steps={intervalSteps}"
  (← IO.getStdout).flush
  let mut passed := true
  for a in statisticalCandidates do
    let ok ← report a validation
    passed := passed && ok
  return if passed then 0 else 1
