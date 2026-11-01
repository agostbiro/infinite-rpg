import Rpg.Mechanic

/-!
# The rules of one adventure

Each adventure has one `RuleSet` value, in its own `Rules.lean`. The spec, the checker, the
Engine, and the balance check all get that same value. The default of each field is the
GURPS Lite rule in `Rpg/Rules.lean`, so `{}` means "the rules of this game, unchanged".

A `RuleSet` is part of what "legal" means. People own the `Rules.lean` files: `make check`
fails if a `Rules.lean` is not `{}`, unless a person puts its path on the allow list.
-/
namespace Rpg

/-- The limits and the rules of one adventure. Each field defaults to the rule in `Rpg/Rules.lean`. -/
structure RuleSet where
  /-- The lowest attribute score a Creature may have. -/
  creatureAttributeMin : Nat := 1
  /-- The highest attribute score a Creature may have. -/
  creatureAttributeMax : Nat := 20
  /-- The most points a Creature may cost. -/
  creaturePointLimit : Int := 150
  /-- The lowest attribute score the Character may have. -/
  characterAttributeMin : Nat := 7
  /-- The highest attribute score the Character may have. -/
  characterAttributeMax : Nat := 14
  /-- The exact number of points the Character must cost. -/
  characterPoints : Int := 100
  /-- The most natural DR the Character may have. -/
  characterNaturalDRLimit : Nat := 0
  /-- The lowest modifier a Success Roll in a Scene may have. -/
  modifierMin : Int := -10
  /-- The highest modifier a Success Roll in a Scene may have. -/
  modifierMax : Int := 10
  /-- The lowest effective skill at which a being may roll (p. 2). Below it, the roll fails. -/
  minimumRollLevel : Int := 3
  /-- The result of a 3d6 roll against an effective skill (p. 2). -/
  successRoll : Int → Nat → RollResult := Rpg.successRoll
  /-- The full HP of a being. -/
  maxHP : Being → Nat := Being.maxHP
  /-- The Dodge score of a being, before wounds and maneuvers. -/
  dodge : Being → Nat := Being.dodge
  /-- Four times the Basic Speed of a being, for turn order. -/
  speedX4 : Being → Nat := Being.speedX4
  /-- The score of an attribute. -/
  attr : Being → Attribute → Nat := Being.attr
  /-- The level of a being in a skill, or `none` if it cannot use the skill. -/
  skillLevel : Being → Skill → Option Int := Being.skillLevel
  /-- The step that a skill level was bought at, or `none` if it cannot be bought. -/
  skillStep : Being → Skill → Nat → Option Nat := Being.skillStep
  /-- The point cost of a being. -/
  points : Being → Int := Being.points
  /-- The level at which a being attacks with its weapon. -/
  attackLevel : Being → Int := Being.attackLevel
  /-- The lowest ST that can use a weapon. -/
  minST : Weapon → Nat := Weapon.minST
  /-- The damage dice of a weapon at a given ST. -/
  damage : Weapon → Nat → Dice := Weapon.damage
  /-- Basic damage from the dice and their sum. -/
  basicDamage : Dice → DamageType → Nat → Nat := Rpg.basicDamage
  /-- Injury from damage type, DR, and basic damage. -/
  injury : DamageType → Nat → Nat → Nat := Rpg.injury
  /-- The DR of a being. -/
  dr : Being → Nat := Being.dr
  /-- `true`: a being with less than 1/3 of its HP has its Dodge halved (p. 29). -/
  halveDodgeBelowThird : Bool := true
  /-- `true`: the Character wins a tie in turn order that is left after Speed and DX. -/
  heroWinsInitiativeTies : Bool := true
  /-- Equipment granted inside this Adventure, including its actual attack and damage values. -/
  equipment : List EquipmentRule := []
  /-- Named conditional effects active only in this Adventure. -/
  combatRules : List CombatRule := []

/-- Equipment affects only its named owner using its specified weapon. -/
def RuleSet.equipmentFor (rules : RuleSet) (b : Being) : Option EquipmentRule :=
  rules.equipment.find? fun e => e.owner == b.name && e.weapon == b.weapon

/-- The attack level of the equipped weapon, before maneuvers and conditional effects. -/
def RuleSet.weaponLevel (rules : RuleSet) (b : Being) : Int :=
  match rules.equipmentFor b with
  | some e => e.attackLevel
  | none => rules.attackLevel b

/-- Equipment damage uses the same dice in play, simulation, and the graph. -/
def RuleSet.weaponDice (rules : RuleSet) (b : Being) : Dice :=
  match rules.equipmentFor b with
  | some e => ⟨e.dice, e.add⟩
  | none => rules.damage b.weapon b.st

/-- Remove the two data fields that an in-play proposal is allowed to change. -/
def RuleSet.core (rules : RuleSet) : RuleSet :=
  { rules with equipment := [], combatRules := [] }

/-- Every possible sum of n fair d6, including zero when n is zero. -/
def possibleDiceSums (n : Nat) : List Nat :=
  (List.range (5 * n + 1)).map (· + n)

/-- Use every negative hit effect for the state-independent fight legality check. -/
def RuleSet.checkedAttackLevel (rules : RuleSet) (b : Being) : Int :=
  rules.weaponLevel b + (rules.combatRules.map fun r => min 0 r.hitBonus).sum

/-- Use every negative damage effect for the state-independent fight legality check. -/
def RuleSet.checkedDamage (rules : RuleSet) (b : Being) : Dice :=
  let dice := rules.weaponDice b
  { dice with add := dice.add + (rules.combatRules.map fun r => min 0 r.damageBonus).sum }

/-- Include all possible extra armor, even when some triggers or sides cannot coincide. -/
def RuleSet.checkedArmor (rules : RuleSet) (b : Being) : Nat :=
  rules.dr b + (rules.combatRules.map (·.armorBonus)).sum

/-- Check for an attack that can hit, pass Dodge, and cause injury with conservative effects.
Negative hit/damage effects and all extra armor count regardless of their side or trigger;
positive offensive effects do not help this check. This can reject some playable fights. -/
def RuleSet.canHurt (rules : RuleSet) (a b : Being) : Prop :=
  rules.minimumRollLevel ≤ rules.checkedAttackLevel a ∧
  ∃ roll ∈ possibleDiceSums 3,
    (rules.successRoll (rules.checkedAttackLevel a) roll).succeeded = true ∧
    ((rules.successRoll (rules.checkedAttackLevel a) roll) = .criticalSuccess ∨
      ∃ defense ∈ possibleDiceSums 3,
        (rules.successRoll (rules.dodge b) defense).succeeded = false) ∧
    ∃ damageRoll ∈ (if roll = 3 then [6 * (rules.checkedDamage a).count]
        else possibleDiceSums (rules.checkedDamage a).count),
      0 < rules.injury a.weapon.damageType (rules.checkedArmor b)
        (rules.basicDamage (rules.checkedDamage a) a.weapon.damageType damageRoll)

instance (rules : RuleSet) (a b : Being) : Decidable (rules.canHurt a b) := by
  unfold RuleSet.canHurt
  infer_instance

end Rpg
