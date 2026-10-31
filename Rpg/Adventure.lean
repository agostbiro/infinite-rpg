import Rpg.Rules

/-!
# Adventures

An Adventure is a graph of Scenes. Each Scene has text and a list of Choices.
A Choice leads to another Scene directly, through a Success Roll, or through a Fight.
A Scene with no Choices is an Ending.

The types here have no way to say "the Character loses HP" or "the Character dies".
So an Adventure cannot script harm. Harm only comes from a Fight, which the Engine runs.
-/

namespace Rpg

/-- A Scene is named by a number. -/
abbrev SceneId := Nat

/-- What a Success Roll is made against: a skill or an attribute. -/
inductive RollTarget where
  | skill (s : Skill)
  | attribute (a : Attribute)
  deriving Repr

/-- The level of a being for a Success Roll against a target, before modifiers.
`none` means the being cannot use the skill, not even at its default. -/
def Being.rollLevel (b : Being) : RollTarget → Option Int
  | .skill s => b.skillLevel s
  | .attribute a => some (b.attr a)

/-- The name of a roll target, for display. -/
def RollTarget.name : RollTarget → String
  | .skill s => s.name
  | .attribute .st => "ST"
  | .attribute .dx => "DX"
  | .attribute .iq => "IQ"
  | .attribute .ht => "HT"

/-- What happens when the Player picks a Choice. -/
inductive Outcome where
  /-- Go to a Scene. -/
  | goto (next : SceneId)
  /-- Make a Success Roll at a modifier, then go to one of two Scenes. -/
  | roll (target : RollTarget) (modifier : Int) (onSuccess onFailure : SceneId)
  /-- Fight these Creatures. If the Character wins, go to `onWin`. If the Character dies, the game ends. -/
  | fight (foes : List Being) (onWin : SceneId)
  deriving Repr

/-- An option the Player can pick in a Scene. -/
structure Choice where
  text : String
  outcome : Outcome
  deriving Repr

/-- One step of an Adventure. -/
structure Scene where
  id : SceneId
  title : String
  text : String
  choices : List Choice
  deriving Repr

/-- A complete scenario, written before play. -/
structure Adventure where
  title : String
  start : SceneId
  scenes : List Scene
  deriving Repr

/-- Find a Scene by its number. -/
def Adventure.scene? (a : Adventure) (id : SceneId) : Option Scene :=
  a.scenes.find? (·.id == id)

/-- Every Scene that an Outcome can lead to. -/
def Outcome.targets : Outcome → List SceneId
  | .goto n => [n]
  | .roll _ _ s f => [s, f]
  | .fight _ w => [w]

/-- The Creatures in an Outcome. -/
def Outcome.foes : Outcome → List Being
  | .fight fs _ => fs
  | _ => []

end Rpg
