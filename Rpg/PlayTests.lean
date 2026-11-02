import Rpg.Play
import Rpg.RuntimeInvariant
import Rpg.Adventures.TestAdventure

namespace Rpg

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
  order := turnOrder TestAdventure.rules TestAdventure.mara [TestAdventure.bandit 1, TestAdventure.bandit 2]
  round := 2
  state := {
    hero := { being := TestAdventure.mara, hp := 9 },
    foes := [{ being := TestAdventure.bandit 1, hp := -1 }, { being := TestAdventure.bandit 2, hp := 4 }] }

/-- A game in the Fight `banditFight`. -/
def fightGame : Game := { titleGame with hp := banditFight.state.hero.hp, phase := .fight banditFight }

/-- A game that reached an Ending. -/
def endedGame : Game := { titleGame with phase := .ended 8 }

-- The execution fixtures satisfy the same consistency predicate preserved by `step`.
example : titleGame.WellFormed := Game.new_wellFormed _
example : roadGame.WellFormed := by decide +kernel
example : fightGame.WellFormed := by
  refine ⟨rfl, by decide +kernel, ?_⟩
  exact ⟨_, _, [TestAdventure.bandit 1, TestAdventure.bandit 2],
    rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel⟩
example : endedGame.WellFormed := by decide +kernel

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


/-! ## Execution tests -/


-- Seed 7 gives the faces 4, 1, 1 for the first 3d6.
#guard ((rollDice 3).run' ⟨7⟩).run == [4, 1, 1]

-- The hypothesis of `inputs_allowed` can hold: The Road offers its second Choice.
example : AllowedInput roadGame (.choose 1) := inputs_allowed (by decide)

-- The hypothesis of `step_rejects` can hold: the title screen does not offer a Choice.
-- A refused input leaves the game and the dice as they were.
example : (step titleGame (.choose 0)).run ⟨7⟩ = ((titleGame, [.rejected rejectedWhy]), ⟨7⟩) :=
  step_rejects _ _ _ (by decide)

-- `begin` goes to The Road and rolls no dice.
#guard
  let ((g, reports), dice) := (step titleGame .begin).run ⟨7⟩
  g.phase.name == "scene" && g.sceneId? == some 0 && dice.state == 7 &&
    reports.map (·.isRejected) == [false]

-- With seed 7, the bank (DX -2, so 10 or less) rolls 4, 1, 1 = 6: a success. Mara reaches The Wall Top.
#guard
  let (g, reports) := (step roadGame (.choose 1)).run' ⟨7⟩
  g.sceneId? == some 2 && g.trail.map (·.rolled) == [some true] &&
    reports.contains (.successRoll "Mara" (.attribute .dx) (-2) ⟨[4, 1, 1], 6, 10, .success⟩)

-- In a Fight, a forged attack on a Creature that is down is refused.
#guard
  let (g, reports) := (step fightGame (.maneuver .attack (some 0))).run' ⟨7⟩
  g.phase.name == "fight" && reports == [.rejected rejectedWhy]

/-- Play the first input the game offers, at most `n` times. Returns the last game and all Reports. -/
def autoplay (g : Game) (dice : Rng) : Nat → Game × List Report
  | 0 => (g, [])
  | n + 1 =>
    match g.inputs with
    | [] => (g, [])
    | i :: _ =>
      let ((g, first), dice) := (step g i).run dice
      let (g, later) := autoplay g dice n
      (g, first ++ later)

-- For seeds 0 to 29, the game is over within 200 inputs, by an Ending or by death,
-- and the Engine never refuses an input it offered.
#guard (List.range 30).all fun seed =>
  let (g, reports) := autoplay titleGame ⟨seed.toUInt64⟩ 200
  g.inputs.isEmpty && (g.phase.name == "ended" || g.phase.name == "dead") &&
    !reports.any (·.isRejected)


end Rpg
