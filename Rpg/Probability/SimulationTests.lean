import Rpg.Probability.Simulation
import Rpg.Probability.RuleSetExamples
import Rpg.Probability.TestStory
import Rpg.Play

namespace Rpg.Probability.Simulation
open TestStory

-- A safe ending occurs on its actual scene-choice turn.
#guard ((trajectory safeDefinition 2 6
  safeStory.start (({} : RuleSet).maxHP Lighthouse.mara) 0).run ⟨7⟩).1 == ⟨.ended, 1⟩
-- Fuel exhaustion is recorded as unknown, not as an ending or death.
#guard ((trajectory safeDefinition 2 0
  safeStory.start (({} : RuleSet).maxHP Lighthouse.mara) 0).run ⟨7⟩).1 == ⟨.censored, 1⟩
-- A completed fight is recognized even when no further round budget remains.
#guard ((fight fixtureRules pickManeuver [] 0
  { hero := { being := strongHero, hp := 3 }, foes := [] }).run ⟨7⟩).1.isSome
-- A genuine unresolved fight is not classified as a loss.
#guard ((fight failureRules pickManeuver (turnOrder failureRules strongHero [harmlessFoe]) 2
  { hero := { being := strongHero, hp := 3 }, foes := [{ being := harmlessFoe, hp := 1 }] }).run ⟨7⟩).1.isNone

/-- Play a Fight to its end the way the page does, with `Game.characterTurn`: the Character
always uses Attack on Creature 0. -/
private def playToEnd : Nat → Game → Roll Game
  | 0, g => pure g
  | n + 1, g => match g.phase with
    | .fight f => do
      let (g, _) ← g.characterTurn f .attack (some 0)
      playToEnd n g
    | _ => pure g

/-- The Character's HP at the end of the Fight with Grey Hollis, played as on the page. -/
private def playedHP (seed : Nat) : Int :=
  let g := Game.new Lighthouse.lighthouseDefinition
  ((do
    let (g, _) ← g.startFight 6 0 [Lighthouse.hollis] 8
    playToEnd 200 g).run' ⟨seed.toUInt64⟩).hp

/-- The Character's HP at the end of the same Fight in the simulator, with the same Player. -/
private def simulatedHP (seed : Nat) : Option Int :=
  let r := Lighthouse.rules
  let hero : Fighter := { being := Lighthouse.mara, hp := r.maxHP Lighthouse.mara }
  let foes : List Fighter := [{ being := Lighthouse.hollis, hp := r.maxHP Lighthouse.hollis }]
  ((fight r (fun _ => pure (.attack, 0)) (turnOrder r Lighthouse.mara [Lighthouse.hollis]) 200
    { hero, foes }).run' ⟨seed.toUInt64⟩).map (·.hero.hp)

-- Play and the simulator use the same turn order and the same dice: from the same seed, the
-- Fight ends with the same HP. (With one Creature, the Player's choice uses no random number.)
#guard (List.range 30).all fun seed => simulatedHP seed == some (playedHP seed)

end Rpg.Probability.Simulation
