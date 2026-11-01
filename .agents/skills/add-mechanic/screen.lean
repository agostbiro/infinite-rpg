import Rpg.Catalog

/-!
Screen every adventure in `statisticalCandidates` before the real admission run.
It plays games the same way as `validateCounts`, but with its own seed and
fewer samples, so tuning on it does not spend the held-out validation seed.
Run from the repo root: `lake env lean .agents/skills/add-mechanic/screen.lean`.
This is an estimate, not admission evidence.
-/
open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- An exploratory seed. It must differ from `validationSeed`. -/
def screenSeed : Nat := 1

/-- Observations per row. Fewer than `confidenceSamples`, so the run is fast. -/
def screenSamples : Nat := 20000

/-- The screen gives up after this many games. This keeps the games-per-row
limit of admission: 2,000,000 / 160,000 = 250,000 / 20,000. -/
def screenMaxGames : Nat := 250000

#guard screenMaxGames * confidenceSamples == validationMaxGames * screenSamples

#guard screenSeed != validationSeed

/-- Add one observation to a row unless the row is full. -/
def observe (c : ValidationCounts) (row : Nat) (death : Bool) : ValidationCounts :=
  if c.trials[row]! ≥ screenSamples then c
  else { c with
    trials := c.trials.modify row (· + 1)
    deaths := c.deaths.modify row (· + if death then 1 else 0) }

/-- The same counting as `validateCounts`, with the screen's seed and sizes. -/
def screenCounts (a : StatisticalCandidate) : ValidationCounts := Id.run do
  let h := a.horizon
  let mut counts : ValidationCounts := ⟨Array.replicate (h+1) 0, Array.replicate (h+1) 0, 0, false⟩
  let mut rng : Rng := ⟨screenSeed.toUInt64⟩
  for _ in [:screenMaxGames] do
    if counts.trials.all (· == screenSamples) then break
    let (trace, next) := (Estimate.trajectory a.toAdventureDefinition validationRoundLimit (h+1)
      a.story.start (a.rules.maxHP a.hero) 0).run rng
    rng := next
    counts := { counts with games := counts.games + 1 }
    if !observationsComplete h trace then
      return { counts with aborted := true }
    counts := observe counts 0 (trace.finish == .dead && trace.turn == 1)
    for t in [:h] do
      if t < trace.turn then
        counts := observe counts (t+1) (trace.finish == .dead && trace.turn == t+2)
  return counts

/-- A probability from 0 to 1 as a percent with two decimals, rounded down. -/
def percent (r : Rat) : String :=
  let hundredths := r.num * 10000 / r.den
  let cents := hundredths % 100
  s!"{hundredths / 100}.{if cents < 10 then "0" else ""}{cents}%"

/-- The death frequencies that admission accepts for a band, from `acceptsCount`. -/
def passRange (b : Band) : Rat × Rat :=
  let low := if b.target - b.tolerance ≤ 0 then 0 else b.target - b.tolerance + confidenceEpsilon
  let high := if 1 ≤ b.target + b.tolerance then 1 else b.target + b.tolerance - confidenceEpsilon
  (low, high)

/-- Print each row's frequency next to the range that admission accepts. -/
def report (a : StatisticalCandidate) : IO Unit := do
  let c := screenCounts a
  IO.println s!"== {a.story.title} (horizon {a.horizon}, {c.games} games)"
  if c.aborted then
    IO.println "ABORTED: a fight hit the round limit or a game was invalid inside the window."
    return
  for row in [:a.horizon + 1] do
    let some i := (if h : row < a.horizon + 1 then some (⟨row, h⟩ : Fin (a.horizon + 1)) else none)
      | continue
    let n := c.trials[row]!
    let k := c.deaths[row]!
    let name := if row = 0 then "death on turn 1" else s!"death on turn {row + 1} given alive at turn {row - 1}"
    let band := confidenceBands a.horizon i
    let (low, high) := passRange band
    if n < screenSamples then
      IO.println s!"{name}: NOT FILLED, {n} of {screenSamples} observations. Too few games reach this turn."
    else
      let freq : Rat := (k : Rat) / (n : Rat)
      let verdict := if low ≤ freq ∧ freq ≤ high then "ok" else "FAIL"
      IO.println s!"{name}: {percent freq}, must be {percent low} to {percent high}: {verdict}"

#eval do
  for a in statisticalCandidates do
    report a
