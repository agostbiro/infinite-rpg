import Rpg.Adventures.Lighthouse.Story
import Rpg.Probability.StatisticalAdmission

/-!
Check that the model and the simulation agree on one fight.
The model's death chance comes from `combatDistribution`; the simulation's from
`validationGames` runs of `Simulation.fight`. Both use the same Player: each maneuver
with chance 1/3, then a random living target, with the admission round limit.
The check says `ok` when the model's chance is inside the simulation's exact
binomial interval at the admission confidence level (`confidenceDelta`).
`DISAGREE` flags a discrepancy, but sampling alone can also produce it with probability
at most `confidenceDelta` under the sampling model (currently 5%). Before you conclude,
run a larger simulation with another seed (for example 20,000 Fights).
Run as compiled code: `lake exe agree`. The exact model takes minutes for a Lighthouse Fight,
whatever the simulation run count.
-/
open Rpg Rpg.Probability Rpg.Probability.Confidence

/-- A fight to check: a name, the rules, the hero, and the foes. -/
structure FightCase where
  name : String
  rules : RuleSet
  hero : Being
  foes : List Being

/-- The fights to check. Add one fight from each target story that has fights. -/
def cases : List FightCase :=
  [⟨"Lighthouse: Grey Hollis", Lighthouse.rules, Lighthouse.mara, [Lighthouse.hollis]⟩,
   ⟨"Lighthouse: two wreckers", Lighthouse.rules, Lighthouse.mara,
     [Lighthouse.wrecker 1, Lighthouse.wrecker 2]⟩]

/-- This check uses its own seed. The validation seed stays held out. -/
def agreeSeed : Nat := 7

#guard agreeSeed != validationSeed

/-- The model's chance that the hero dies, starting at full HP. -/
def modelDeath (c : FightCase) : Rat :=
  (combatDistribution c.rules c.hero (c.rules.maxHP c.hero) c.foes).mass (· == .died)

/-- Simulated fights: the number of hero deaths, and the number of fights that hit the round limit. -/
def simulate (c : FightCase) : Nat × Nat := Id.run do
  let mut rng : Rng := ⟨agreeSeed.toUInt64⟩
  let mut deaths := 0
  let mut timeouts := 0
  for _ in [:validationGames] do
    let hero : Fighter := { being := c.hero, hp := c.rules.maxHP c.hero }
    let foes : List Fighter := c.foes.map fun f => { being := f, hp := c.rules.maxHP f }
    let start : FightState := { hero, foes }
    let (result, next) := (Simulation.fight c.rules Simulation.pickManeuver
      (turnOrder c.rules c.hero c.foes) validationRoundLimit start).run rng
    rng := next
    match result with
    | some s => if !s.hero.alive then deaths := deaths + 1
    | none => timeouts := timeouts + 1
  return (deaths, timeouts)

/-- A probability from 0 to 1 as a percent with two decimals, rounded down. -/
def percent (r : Rat) : String :=
  let hundredths := r.num * 10000 / r.den
  let cents := hundredths % 100
  s!"{hundredths / 100}.{if cents < 10 then "0" else ""}{cents}%"

/-- Print one line per fight in `cases`: `ok`, `DISAGREE`, or `ABORTED`. -/
def main : IO UInt32 := do
  IO.println s!"Agreement: {validationGames} simulated fights per case; round limit={validationRoundLimit}; interval failure bound={confidenceDelta}; endpoint steps={intervalSteps}"
  let mut passed := true
  for c in cases do
    IO.println s!"Checking {c.name} (exact model and simulated fights)..."
    (← IO.getStdout).flush
    let model := modelDeath c
    let (deaths, timeouts) := simulate c
    if timeouts > 0 then
      IO.println s!"{c.name}: ABORTED: {timeouts} fights hit the round limit"
      passed := false
      continue
    let interval := confidenceInterval confidenceDelta validationGames deaths
    let ok := decide (interval.Contains model)
    passed := passed && ok
    let verdict := if ok then "ok" else "DISAGREE"
    IO.println s!"{c.name}: model {percent model}, simulation {deaths}/{validationGames}, interval [{percent interval.lower}, {percent interval.upper}]: {verdict}"
  return if passed then 0 else 1
