import Rpg.Rules

/-! Adventure-local equipment and combat effects are data. They cannot change dice,
turn order, character budgets, or the balance policy. The same effects run in play
and in the probability model. -/
namespace Rpg

/-- A named hero equipment profile, using a supported weapon's attack type.
`owner` never authorizes an enemy: lookup also requires the actual hero actor. -/
structure EquipmentRule where
  owner : String
  weapon : Weapon
  name : String
  attackLevel : Nat
  dice : Nat
  add : Int
  deriving DecidableEq, Repr

/-- Mechanic sides are checked once at the JSON boundary. -/
inductive CombatSide where
  | hero | foes
  deriving DecidableEq, Repr

def CombatSide.all : List CombatSide := [.hero, .foes]
def CombatSide.key : CombatSide → String
  | .hero => "hero"
  | .foes => "foes"

/-- Every supported condition; the engine must handle each constructor. -/
inductive CombatTrigger where
  | always | wounded | desperate | reckless | guarding
  | againstReckless | againstGuarding | againstFlame
  deriving DecidableEq, Repr

def CombatTrigger.all : List CombatTrigger :=
  [.always, .wounded, .desperate, .reckless, .guarding, .againstReckless, .againstGuarding, .againstFlame]

def CombatTrigger.key : CombatTrigger → String
  | .always => "always"
  | .wounded => "wounded"
  | .desperate => "desperate"
  | .reckless => "reckless"
  | .guarding => "guarding"
  | .againstReckless => "againstReckless"
  | .againstGuarding => "againstGuarding"
  | .againstFlame => "againstFlame"

theorem CombatTrigger.mem_all (t : CombatTrigger) : t ∈ CombatTrigger.all := by
  cases t <;> decide

/-- A conditional combat effect. The decoder checks the side, trigger, and numeric limits. -/
structure CombatRule where
  name : String
  description : String
  side : CombatSide
  trigger : CombatTrigger
  hitBonus : Int := 0
  damageBonus : Int := 0
  armorBonus : Nat := 0
  deriving DecidableEq, Repr

/-- Supported triggers depend only on current HP, maneuvers, and equipment. -/
def combatTriggers : List String :=
  CombatTrigger.all.map CombatTrigger.key

/-- Only a hero effect or an enemy effect is allowed. -/
def CombatRule.forHero (r : CombatRule) (hero : Bool) : Bool :=
  if hero then r.side == .hero else r.side == .foes

/-- A committed attack hits harder, at the cost of the maneuver's exposed defense. -/
def committedStrike : CombatRule := {
  name := "Committed Strike", description := "Your All-Out Attack gains +1 damage per hit. You still cannot Dodge.",
  side := .hero, trigger := .reckless, damageBonus := 1 }

/-- Guarding draws an enemy into a feint instead of adding passive armor. -/
def guardFeint : CombatRule := {
  name := "Guard Feint", description := "While you use All-Out Defense, enemies have -1 to hit you.",
  side := .foes, trigger := .againstGuarding, hitBonus := -1 }

/-- A wounded enemy becomes more accurate, making target priority matter. -/
def corneredFury : CombatRule := {
  name := "Cornered Fury", description := "Enemies at half HP or less gain +2 to hit. Finish a wounded enemy before it rallies.",
  side := .foes, trigger := .wounded, hitBonus := 2 }

/-- Reckless offense invites a stronger response, distinct from the hero's damage bonus. -/
def punishOpening : CombatRule := {
  name := "Punish the Opening", description := "Enemies gain +1 damage per hit against your All-Out Attack.",
  side := .foes, trigger := .againstReckless, damageBonus := 1 }

/-- Shared adventure defaults: every built-in or generated game inherits these tactical rules. -/
def defaultCombatRules : List CombatRule :=
  [committedStrike, guardFeint, corneredFury, punishOpening]

end Rpg
