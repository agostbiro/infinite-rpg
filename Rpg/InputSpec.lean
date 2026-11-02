import Rpg.Game

/-!
# Spec: which inputs the rules allow

The page can send any input. This file says which inputs the rules allow in each game.
`Rpg/Play.lean` proves these things about the Engine:

* `mem_inputs_iff`: the game offers (`Game.inputs`) exactly the inputs allowed here.
* `step_rejects`: an input the game does not offer changes nothing and rolls no dice.

So the Player can do all that the rules allow and nothing else, whatever the page sends.
-/

namespace Rpg

/-- The Fight goes on: the Character is alive and at least one Creature is alive. -/
def FightGoesOn (s : FightState) : Prop :=
  s.hero.alive = true ∧ ∃ foe ∈ s.foes, foe.alive = true

/-- The rules allow input `i` in game `g`.
Only the pairs of phase and input below are allowed. -/
def AllowedInput (g : Game) (i : Input) : Prop :=
  match g.phase, i with
  -- On the title screen, the Player can start play.
  | .title, .begin => True
  -- In a Scene, the Player can pick one of that Scene's Choices.
  | .scene id, .choose k =>
    ∃ sc, g.adventure.scene? id = some sc ∧ k < sc.choices.length
  -- On the Character's turn in a Fight, the Player can attack a living Creature.
  | .fight f, .maneuver m (some t) =>
    FightGoesOn f.state ∧ m.attacks = true ∧
      ∃ foe, f.state.foes[t]? = some foe ∧ foe.alive = true
  -- On the Character's turn in a Fight, the Player can use a Maneuver with no attack.
  -- Such a Maneuver has no target.
  | .fight f, .maneuver m none =>
    FightGoesOn f.state ∧ m.attacks = false
  -- No other input is allowed. For example, nothing is allowed after the Adventure is over.
  | _, _ => False

end Rpg
