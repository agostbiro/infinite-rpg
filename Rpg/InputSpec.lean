import Rpg.Game
import Rpg.Adventures.TestAdventure

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

/-! ## Examples

Each example uses Mara in the test Adventure, The Bandit Camp. -/

/-- A new game on the title screen. -/
def titleGame : Game := Game.new TestAdventure.testAdventureDefinition

/-- A game in The Road, the first Scene. It has 2 Choices. -/
def roadGame : Game := { titleGame with phase := .scene 0 }

/-- A Fight against two bandits, on the Character's turn. Bandit 1 is down, Bandit 2 is alive. -/
def banditFight : FightPhase where
  scene := 4
  choice := 0
  onWin := 5
  order := [none, some 0, some 1]
  round := 2
  state := {
    hero := { being := TestAdventure.mara, hp := 9 },
    foes := [{ being := TestAdventure.bandit 1, hp := -1 }, { being := TestAdventure.bandit 2, hp := 4 }] }

/-- A game in the Fight `banditFight`. -/
def fightGame : Game := { titleGame with phase := .fight banditFight }

/-- A game that reached an Ending. -/
def endedGame : Game := { titleGame with phase := .ended 8 }

-- Allowed: start play on the title screen.
example : AllowedInput titleGame .begin := trivial

-- Allowed: pick the second Choice of The Road.
example : AllowedInput roadGame (.choose 1) := ⟨_, rfl, by decide⟩

/-- In `banditFight`, the Fight goes on. -/
theorem banditFight_goesOn : FightGoesOn banditFight.state :=
  ⟨rfl, _, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

-- Allowed: an All-Out Attack on Bandit 2, who is alive.
example : AllowedInput fightGame (.maneuver .allOutAttack (some 1)) :=
  ⟨banditFight_goesOn, rfl, _, rfl, rfl⟩

-- Allowed: All-Out Defense, with no target.
example : AllowedInput fightGame (.maneuver .allOutDefense none) :=
  ⟨banditFight_goesOn, rfl⟩

-- Rejected: The Road has no third Choice.
example : ¬ AllowedInput roadGame (.choose 2) := by
  rintro ⟨sc, hsc, hk⟩
  simp [roadGame, titleGame, Game.new, TestAdventure.testAdventureDefinition, TestAdventure.testAdventure, Adventure.scene?] at hsc
  subst hsc
  simp at hk

-- Rejected: play has already started.
example : ¬ AllowedInput roadGame .begin := id

-- Rejected: Bandit 1 is down, so the Character cannot attack it.
example : ¬ AllowedInput fightGame (.maneuver .attack (some 0)) := by
  rintro ⟨_, _, foe, hfoe, halive⟩
  simp [banditFight] at hfoe
  subst hfoe
  simp [Fighter.alive] at halive

-- Rejected: there is no Creature number 5.
example : ¬ AllowedInput fightGame (.maneuver .attack (some 5)) := by
  rintro ⟨_, _, foe, hfoe, _⟩
  simp [banditFight] at hfoe

-- Rejected: All-Out Defense does not attack, so it cannot have a target.
example : ¬ AllowedInput fightGame (.maneuver .allOutDefense (some 1)) := by
  rintro ⟨_, hattacks, _⟩
  simp [Maneuver.attacks] at hattacks

-- Rejected: an Attack needs a target.
example : ¬ AllowedInput fightGame (.maneuver .attack none) := by
  rintro ⟨_, hattacks⟩
  simp [Maneuver.attacks] at hattacks

-- Rejected: in a Fight, the Player cannot pick a Choice of the Scene.
example : ¬ AllowedInput fightGame (.choose 0) := id

-- Rejected: after an Ending, no input is allowed.
example : ¬ AllowedInput endedGame (.choose 0) := id

/-- A Fight where both bandits are down. The Fight is over. -/
def wonFight : FightPhase :=
  { banditFight with state := { banditFight.state with
      foes := [{ being := TestAdventure.bandit 1, hp := -1 }, { being := TestAdventure.bandit 2, hp := 0 }] } }

-- Rejected: the Fight is over, so the Character cannot choose a Maneuver.
example : ¬ AllowedInput { titleGame with phase := .fight wonFight } (.maneuver .allOutDefense none) := by
  rintro ⟨⟨_, foe, hfoe, halive⟩, _⟩
  simp [wonFight, banditFight] at hfoe
  rcases hfoe with rfl | rfl <;> simp [Fighter.alive] at halive

end Rpg
