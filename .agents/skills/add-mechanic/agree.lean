import Rpg.Adventures.Lighthouse.Story
import Rpg.Probability.Simulation

/-!
Check that the model and the simulation agree on one fight.
The model's death chance comes from `combatDistribution`; the simulation's from
many runs of `Simulation.fight`. A gap of 1 point or more means the mechanic
reaches one path but not the other.
Run from the repo root: `lake env lean .agents/skills/add-mechanic/agree.lean`.
-/
open Rpg Rpg.Probability

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

/-- Simulated fights per case. -/
def runs : Nat := 20000

/-- The model's chance that the hero dies, starting at full HP. -/
def modelDeath (c : FightCase) : Rat :=
  (combatDistribution c.rules c.hero (c.rules.maxHP c.hero) c.foes).mass (· == .died)

/-- The fraction of simulated fights the hero loses. A fight that hits the round limit counts as no death. -/
def simulatedDeath (c : FightCase) : Rat := Id.run do
  let mut rng : Rng := ⟨7⟩
  let mut deaths := 0
  for _ in [:runs] do
    let start : FightState := ⟨⟨c.hero, c.rules.maxHP c.hero⟩, c.foes.map fun f => ⟨f, c.rules.maxHP f⟩⟩
    let (result, next) := (Simulation.fight c.rules (turnOrder c.rules c.hero c.foes) 200 start).run rng
    rng := next
    if let some s := result then
      if !s.hero.alive then deaths := deaths + 1
  return (deaths : Rat) / (runs : Rat)

/-- A probability from 0 to 1 as a percent with two decimals, rounded down. -/
def percent (r : Rat) : String :=
  let hundredths := r.num * 10000 / r.den
  let cents := hundredths % 100
  s!"{hundredths / 100}.{if cents < 10 then "0" else ""}{cents}%"

#eval do
  for c in cases do
    let model := modelDeath c
    let sim := simulatedDeath c
    let gap := if model ≤ sim then sim - model else model - sim
    let verdict := if gap < 1 / 100 then "ok" else "DISAGREE"
    IO.println s!"{c.name}: model {percent model}, simulation {percent sim}: {verdict}"
