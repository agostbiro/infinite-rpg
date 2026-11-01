import Rpg.Adventures.Lighthouse.Story
import Rpg.Probability.StatisticalAdmission

/-!
Check that the model and the simulation agree on one fight.
The model's death chance comes from `combatDistribution`; the simulation's from
`validationGames` runs of `Simulation.fight`, with the admission round limit.
The check says `ok` when the model's chance is inside the simulation's exact
binomial interval at the admission confidence level (`confidenceDelta`).
`DISAGREE` means the mechanic reaches one path but not the other.
Run from the repo root: `lake exe agree`. It runs as compiled code; the exact model is too slow in the interpreter.
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
    let start : FightState := ⟨⟨c.hero, c.rules.maxHP c.hero⟩, c.foes.map fun f => ⟨f, c.rules.maxHP f⟩⟩
    let (result, next) :=
      (Simulation.fight c.rules (turnOrder c.rules c.hero c.foes) validationRoundLimit start).run rng
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
def main : IO Unit := do
  for c in cases do
    let model := modelDeath c
    let (deaths, timeouts) := simulate c
    if timeouts > 0 then
      IO.println s!"{c.name}: ABORTED: {timeouts} fights hit the round limit"
      continue
    let interval := confidenceInterval confidenceDelta validationGames deaths
    let verdict := if interval.Contains model then "ok" else "DISAGREE"
    IO.println s!"{c.name}: model {percent model}, simulation {deaths}/{validationGames}, interval [{percent interval.lower}, {percent interval.upper}]: {verdict}"
