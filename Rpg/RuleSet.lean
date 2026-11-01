import Rpg.Rules

/-! Shared rule interfaces. Each adventure owns a `RuleSet` value; the engine,
checker, and probability model all consume that same value. Field defaults are
reusable GURPS Lite mechanics, not a globally selected adventure ruleset. -/
namespace Rpg

/-- Adventure-specific build constraints and executable game mechanics. -/
structure RuleSet where
  creatureAttributeMin : Nat := 1
  creatureAttributeMax : Nat := 20
  creaturePointLimit : Int := 150
  characterAttributeMin : Nat := 7
  characterAttributeMax : Nat := 14
  characterPoints : Int := 100
  characterNaturalDRLimit : Nat := 0
  modifierMin : Int := -10
  modifierMax : Int := 10
  minimumRollLevel : Int := 3
  successRoll : Int → Nat → RollResult := Rpg.successRoll
  maxHP : Being → Nat := Being.maxHP
  dodge : Being → Nat := Being.dodge
  speedX4 : Being → Nat := Being.speedX4
  attr : Being → Attribute → Nat := Being.attr
  skillLevel : Being → Skill → Option Int := Being.skillLevel
  skillStep : Being → Skill → Nat → Option Nat := Being.skillStep
  points : Being → Int := Being.points
  attackLevel : Being → Int := Being.attackLevel
  minST : Weapon → Nat := Weapon.minST
  damage : Weapon → Nat → Dice := Weapon.damage
  basicDamage : Dice → DamageType → Nat → Nat := Rpg.basicDamage
  injury : DamageType → Nat → Nat → Nat := Rpg.injury
  dr : Being → Nat := Being.dr
  halveDodgeBelowThird : Bool := true
  heroWinsInitiativeTies : Bool := true

/-- Every possible sum of n fair d6, including zero when n is zero. -/
def possibleDiceSums (n : Nat) : List Nat :=
  (List.range (5 * n + 1)).map (· + n)

/-- An attack can injure a full-health opponent with some possible dice results.
The test uses the adventure's success, dodge, damage, armor, and injury rules. -/
def RuleSet.canHurt (rules : RuleSet) (a b : Being) : Prop :=
  rules.minimumRollLevel ≤ rules.attackLevel a ∧
  ∃ roll ∈ possibleDiceSums 3,
    (rules.successRoll (rules.attackLevel a) roll).succeeded = true ∧
    ((rules.successRoll (rules.attackLevel a) roll) = .criticalSuccess ∨
      ∃ defense ∈ possibleDiceSums 3,
        (rules.successRoll (rules.dodge b) defense).succeeded = false) ∧
    ∃ damageRoll ∈ (if roll = 3 then [6 * (rules.damage a.weapon a.st).count]
        else possibleDiceSums (rules.damage a.weapon a.st).count),
      0 < rules.injury a.weapon.damageType (rules.dr b)
        (rules.basicDamage (rules.damage a.weapon a.st) a.weapon.damageType damageRoll)

instance (rules : RuleSet) (a b : Being) : Decidable (rules.canHurt a b) := by
  unfold RuleSet.canHurt
  infer_instance

end Rpg
