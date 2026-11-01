import Rpg.Rules

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

/-- Every possible sum of n fair d6, including zero when n is zero. -/
def possibleDiceSums (n : Nat) : List Nat :=
  (List.range (5 * n + 1)).map (· + n)

/-- Being `a` can hurt being `b`: `a` can try an attack roll, and some dice results give
an attack that hits, gets past the Dodge of `b`, and does injury. The test uses this
adventure's rules for success, Dodge, damage, DR, and injury. -/
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
