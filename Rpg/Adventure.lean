import Rpg.Rules

/-!
# Adventures

An Adventure is a graph of Scenes. Each Scene has text and a list of Choices.
A Choice leads to another Scene directly, through a Success Roll, or through a Fight.
A Scene with no Choices is an Ending.

An Adventure can also give Theme Names to skills, weapons, and armor, such as "Wand Duelling"
for Broadsword. A Theme Name changes only what the Player sees. The spec and the Engine do not
look at Theme Names.

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
  deriving Repr, DecidableEq

/-- The level of a being for a Success Roll against a target, before modifiers.
`none` means the being cannot use the skill, not even at its default. -/
def Being.rollLevel (b : Being) : RollTarget → Option Int
  | .skill s => b.skillLevel s
  | .attribute a => some (b.attr a)

/-- The short name of an attribute, such as "DX". -/
def Attribute.name : Attribute → String
  | .st => "ST"
  | .dx => "DX"
  | .iq => "IQ"
  | .ht => "HT"

/-- The name of a roll target, for display. -/
def RollTarget.name : RollTarget → String
  | .skill s => s.name
  | .attribute a => a.name

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
  /-- The name of the Picture shown with the Scene: the page shows `web/pictures/<name>.svg`.
  It changes only what the Player sees. The spec and the checker do not look at it. -/
  picture : Option String := none
  deriving Repr

/-- The Theme Names of an Adventure: display names for skills, weapons, and armor.
A thing with no Theme Name shows its rule name. The spec and the Engine do not look at these. -/
structure ThemeNames where
  skills : List (Skill × String) := []
  weapons : List (Weapon × String) := []
  armor : List (Armor × String) := []
  deriving Repr

/-- The name the Player sees for a skill: its Theme Name, or else its rule name. -/
def ThemeNames.skill (th : ThemeNames) (s : Skill) : String :=
  (th.skills.lookup s).getD s.name

/-- The name the Player sees for a weapon: its Theme Name, or else its rule name. -/
def ThemeNames.weapon (th : ThemeNames) (w : Weapon) : String :=
  (th.weapons.lookup w).getD w.name

/-- The name the Player sees for a type of armor: its Theme Name, or else its rule name. -/
def ThemeNames.armorName (th : ThemeNames) (a : Armor) : String :=
  (th.armor.lookup a).getD a.name

/-- A complete scenario, written before play. -/
structure Adventure where
  title : String
  start : SceneId
  scenes : List Scene
  /-- Display names for skills, weapons, and armor. The spec does not look at them. -/
  themes : ThemeNames := {}
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
