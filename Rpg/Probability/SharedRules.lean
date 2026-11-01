import Rpg.Probability.Simulation

/-!
These contracts prevent mechanics from bypassing the shared attack and actor-turn
functions in one execution path. They check routing for all inputs without enumerating
fight outcomes; they do not prove equivalence of the PRNG and the ideal probability law.
-/
namespace Rpg.Probability.SharedRules

/-- Seeded attacks use the shared rules with the engine's dice source. -/
theorem seeded_attack (rules : RuleSet) (att dfn : Fighter) :
    attack rules att dfn = attackWith rules rollDice att dfn := rfl

/-- Model attacks use the same rules with the ideal dice source. -/
theorem model_attack (rules : RuleSet) (att dfn : Fighter) :
    attackDistribution rules att dfn =
      ((fun result => (result.1, ([] : List String))) <$>
        attackWith rules dice att dfn).collect := rfl

/-- Seeded actor turns apply the shared turn function and attack function. -/
theorem seeded_turn (rules : RuleSet) (s : FightState) (target : Nat) (who : Actor) :
    takeTurn rules s target who =
      takeTurnWith (attackWith rules rollDice) s target who := rfl

/-- Model actor turns apply the same turn function with model attacks. -/
theorem model_turn (rules : RuleSet) (s : FightState) (target : Nat) (who : Actor) :
    actorDistribution rules s target who =
      (Prod.fst <$> takeTurnWith (attackDistribution rules) s target who).collect := rfl

/-- A seeded round applies only the shared actor turns in the supplied order. -/
theorem seeded_round (rules : RuleSet) (order : List Actor) (s : FightState) (target : Nat) :
    fightRound rules order s target = (do
      let mut st := s
      let mut log : List String := []
      for who in order do
        let (next, lines) ← takeTurnWith (attackWith rules rollDice) st target who
        st := next
        log := log ++ lines
      return (st, log)) := rfl

/-- The model round ends when no actors remain. -/
theorem model_round_done (rules : RuleSet) (target : Nat) (s : FightState) :
    roundActors rules target [] s = pure s := rfl

/-- Each model round step applies the shared actor turn before the remaining actors. -/
theorem model_round_step (rules : RuleSet) (target : Nat) (who : Actor)
    (rest : List Actor) (s : FightState) :
    roundActors rules target (who :: rest) s =
      (((Prod.fst <$> takeTurnWith (attackDistribution rules) s target who).collect).bind
        (roundActors rules target rest)).collect := rfl

/-- The simulation uses engine rounds and retains the uniform living-target selection. -/
theorem simulation_step (rules : RuleSet) (order : List Actor) (fuel : Nat) (state : FightState) :
    Simulation.fight rules order (fuel + 1) state = (do
      if state.over then return some state
      let living := (state.foes.zipIdx.filter fun (f, _) => f.alive).map Prod.snd
      let target := living.getD (← Simulation.choose living.length) 0
      let (next, _) ← fightRound rules order state target
      Simulation.fight rules order fuel next) := rfl

end Rpg.Probability.SharedRules
