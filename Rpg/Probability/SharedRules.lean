import Rpg.Probability.Simulation

/-!
# Shared rules: play, the simulator, and the model use the same Fight code

These theorems check, for every input, that each path calls the shared Engine functions
(`attackWith`, `heroTurnWith`, `foeTurnsWith`, `roundWith`). Each one is true by `rfl`, so a
change that makes one path skip the shared code breaks the build here. They do not prove that
the seeded generator gives the ideal dice odds.
-/
namespace Rpg.Probability.SharedRules

/-- Seeded attacks use the shared attack with the Engine's dice. -/
theorem seeded_attack (rules : RuleSet) (attId : Actor) (att : Fighter) (dfnId : Actor)
    (dfn : Fighter) :
    attack rules attId att dfnId dfn = attackWith rules rollDice attId att dfnId dfn := rfl

/-- Model attacks use the same shared attack with exact dice odds (the sum as one face). -/
theorem model_attack (rules : RuleSet) (attId : Actor) (att : Fighter) (dfnId : Actor)
    (dfn : Fighter) :
    attackDistribution rules attId att dfnId dfn =
      (fun inj => (inj, ([] : List Report))) <$>
        ((Prod.fst <$> attackWith rules sumAsFaces attId att dfnId dfn).collect) := rfl

/-- In play, the Character's turn is the shared turn with seeded attacks. -/
theorem seeded_hero_turn (rules : RuleSet) (s : FightState) (m : Maneuver) (target : Nat) :
    heroTurn rules s m target = heroTurnWith (attack rules) s m target := rfl

/-- In play, the Creature turns are the shared turns with seeded attacks. -/
theorem seeded_foe_turns (rules : RuleSet) (s : FightState) (actors : List Actor) :
    foeTurns rules s actors = foeTurnsWith (attack rules) s actors := rfl

/-- The model's round runs the shared turns in the shared order: the Creatures before the
Character, the Character with the model's Player, then the Creatures after it. -/
theorem model_round (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) :
    roundDistribution rules policy order s =
      ((((foesDistribution rules s (beforeCharacter order)).bind fun s =>
        if s.over then pure s
        else (policy s).bind fun (m, t) =>
          Prod.fst <$> heroTurnWith (attackDistribution rules) s m t).collect).bind
        fun s => foesDistribution rules s (afterCharacter order)).collect := rfl

/-- Each Creature turn in the model is the shared Creature turn with model attacks. -/
theorem model_foe_step (rules : RuleSet) (s : FightState) (a : Actor) (rest : List Actor) :
    foesDistribution rules s (a :: rest) =
      (((Prod.fst <$> foeTurnsWith (attackDistribution rules) s [a]).collect).bind
        fun s => foesDistribution rules s rest).collect := rfl

/-- One step of the simulator is one shared round (`roundWith`) with seeded attacks. -/
theorem simulation_step (rules : RuleSet) (pick : FightState → Roll (Maneuver × Nat))
    (order : List Actor) (fuel : Nat) (state : FightState) :
    Simulation.fight rules pick order (fuel + 1) state = (do
      if state.over then return some state
      let (next, _) ← roundWith (attack rules) pick order state
      Simulation.fight rules pick order fuel next) := rfl

end Rpg.Probability.SharedRules
