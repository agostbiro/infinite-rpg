import Rpg.Catalog

/-!
Screen each adventure with a separate seed and the same fixed game count as admission.
This exploratory batch does not provide admission evidence or permit tuning on the
held-out validation seed. Run: `lake env lean .agents/skills/add-mechanic/screen.lean`.
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

/-- Report exact binomial intervals from the shared sampler using the exploratory seed. -/
def report (a : StatisticalCandidate) : IO Unit := do
  let c := sampleCounts a screenSeed validationGames
  IO.println s!"== {a.story.title} (horizon {a.horizon}, {c.games} games)"
  if c.aborted then
    IO.println "ABORTED: an outcome inside the window was unresolved or invalid."
    return
  for row in [:a.horizon + 1] do
    let some i := (if h : row < a.horizon + 1 then some (⟨row, h⟩ : Fin (a.horizon + 1)) else none)
      | continue
    let count := c.observation row
    let name := if row = 0 then "death on turn 1" else s!"death on turn {row + 1} given active at turn {row - 1}"
    if count.trials = 0 then
      IO.println s!"{name}: NO DATA"
      continue
    let band := confidenceBands a.horizon i
    let interval := confidenceInterval confidenceDelta count.trials count.deaths
    let low := max 0 (band.target - band.tolerance)
    let high := min 1 (band.target + band.tolerance)
    let verdict := if acceptsCount band confidenceDelta count then "ok" else "FAIL"
    IO.println s!"{name}: {count.deaths}/{count.trials}, interval [{percent interval.lower}, {percent interval.upper}], band [{percent low}, {percent high}]: {verdict}"

#eval do
  for a in statisticalCandidates do
    report a
