import Rpg.Rules

/-! Adventure-local equipment and combat effects are data. They cannot change dice,
turn order, character budgets, or the fairness policy. The same effects run in play
and in the probability model. -/
namespace Rpg

/-- A named equipment profile for one being, using a supported weapon's attack type. -/
structure EquipmentRule where
  owner : String
  weapon : Weapon
  name : String
  attackLevel : Nat
  dice : Nat
  add : Int
  deriving DecidableEq, Repr

/-- A conditional combat effect. The decoder checks the side, trigger, and numeric limits. -/
structure CombatRule where
  name : String
  description : String
  side : String
  trigger : String
  hitBonus : Int := 0
  damageBonus : Int := 0
  armorBonus : Nat := 0
  deriving DecidableEq, Repr

/-- Supported triggers depend only on current HP, maneuvers, and equipment. -/
def combatTriggers : List String :=
  ["always", "wounded", "desperate", "reckless", "guarding", "againstReckless", "againstGuarding", "againstFlame"]

/-- Only a hero effect or an enemy effect is allowed. -/
def CombatRule.forHero (r : CombatRule) (hero : Bool) : Bool :=
  if hero then r.side == "hero" else r.side == "foes"

end Rpg
