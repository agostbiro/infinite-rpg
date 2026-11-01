/-!
# Reusable GURPS Lite types and mechanics

This library supplies reusable GURPS Lite defaults: beings, skills, gear,
point costs, damage tables, and success rolls. Each adventure has its own
`RuleSet` (see `Rpg/RuleSet.lean`) in its `Rules.lean`. Play and the balance check get that value as an argument.
Page numbers refer to GURPS Lite, Fourth Edition (2020).
The file `docs/gurps-deviations.md` lists each place where these rules differ from GURPS Lite.
-/

namespace Rpg

/-- The four basic attributes (p. 4). -/
inductive Attribute where
  | st
  | dx
  | iq
  | ht
  deriving Repr, DecidableEq

/-- How hard a skill is to learn (p. 12). -/
inductive Difficulty where
  | easy
  | average
  | hard
  deriving Repr, DecidableEq

/-- The skills in this game (p. 13-17). -/
inductive Skill where
  | broadsword
  | knife
  | brawling
  | stealth
  | lockpicking
  | diplomacy
  | survival
  | naturalist
  | occultism
  | riding
  | climbing
  | swimming
  | firstAid
  | fastTalk
  | staff
  /-- Liquid Projector: the skill to aim a flamethrower (GURPS Basic Set; not in GURPS Lite). -/
  | liquidProjector
  deriving Repr, DecidableEq

/-- Every skill, in a fixed order. -/
def Skill.all : List Skill :=
  [.broadsword, .knife, .brawling, .stealth, .lockpicking, .diplomacy, .survival, .naturalist,
   .occultism, .riding, .climbing, .swimming, .firstAid, .fastTalk, .staff, .liquidProjector]

/-- `Skill.all` lists every skill. -/
theorem Skill.mem_all (s : Skill) : s ∈ Skill.all := by
  cases s <;> decide

/-- The attribute that a skill is based on. -/
def Skill.attribute : Skill → Attribute
  | .broadsword => .dx
  | .knife => .dx
  | .brawling => .dx
  | .stealth => .dx
  | .lockpicking => .iq
  | .diplomacy => .iq
  | .survival => .iq
  | .naturalist => .iq
  | .occultism => .iq
  | .riding => .dx
  | .climbing => .dx
  | .swimming => .ht
  | .firstAid => .iq
  | .fastTalk => .iq
  | .staff => .dx
  | .liquidProjector => .dx

/-- How hard a skill is to learn. -/
def Skill.difficulty : Skill → Difficulty
  | .broadsword => .average
  | .knife => .easy
  | .brawling => .easy
  | .stealth => .average
  | .lockpicking => .average
  | .diplomacy => .hard
  | .survival => .average
  | .naturalist => .hard
  | .occultism => .average
  | .riding => .average
  | .climbing => .average
  | .swimming => .easy
  | .firstAid => .easy
  | .fastTalk => .average
  | .staff => .average
  | .liquidProjector => .easy

/-- The penalty to the attribute when a being uses a skill it has not learned (p. 13-17).
`none` means the being cannot use the skill untrained.
Pages: Climbing and First Aid p. 14; Fast-Talk and Staff p. 15 (a melee skill of Average
difficulty defaults to DX-5); Naturalist, Occultism, and Riding p. 16; Survival and Swimming p. 17. -/
def Skill.defaultPenalty : Skill → Option Int
  | .broadsword => some (-5)
  | .knife => some (-4)
  | .brawling => none
  | .stealth => some (-5)
  | .lockpicking => some (-5)
  | .diplomacy => some (-6)
  | .survival => some (-5)
  | .naturalist => some (-6)
  | .occultism => some (-5)
  | .riding => some (-5)
  | .climbing => some (-5)
  | .swimming => some (-4)
  | .firstAid => some (-4)
  | .fastTalk => some (-5)
  | .staff => some (-5)
  | .liquidProjector => some (-4)

/-- The name of a skill, for display. -/
def Skill.name : Skill → String
  | .broadsword => "Broadsword"
  | .knife => "Knife"
  | .brawling => "Brawling"
  | .stealth => "Stealth"
  | .lockpicking => "Lockpicking"
  | .diplomacy => "Diplomacy"
  | .survival => "Survival"
  | .naturalist => "Naturalist"
  | .occultism => "Occultism"
  | .riding => "Riding"
  | .climbing => "Climbing"
  | .swimming => "Swimming"
  | .firstAid => "First Aid"
  | .fastTalk => "Fast-Talk"
  | .staff => "Staff"
  | .liquidProjector => "Liquid Projector"

/-- The kinds of damage in this game (p. 19). -/
inductive DamageType where
  | crushing
  | cutting
  | impaling
  /-- Fire. Injury equals the damage that gets past DR, as for crushing.
  The lowest basic damage is 1, as for every type except crushing (p. 29). -/
  | burning
  deriving Repr, DecidableEq

/-- A weapon. Each weapon has one attack mode in this version. -/
inductive Weapon where
  /-- Broadsword, swung: sw+1 cutting, ST 10 (p. 20). -/
  | broadsword
  /-- Large knife, thrust: thr impaling, ST 6 (p. 20). -/
  | largeKnife
  /-- Bare-handed punch: thr-1 crushing, no ST minimum (p. 26). -/
  | punch
  /-- Quarterstaff, swung, with Staff skill: sw+2 crushing, ST 7, two hands (p. 20). -/
  | quarterstaff
  /-- Flamethrower: 3d burning, ST 10. It sprays every living foe (deviation 13). -/
  | flamethrower
  deriving Repr, DecidableEq

/-- Every weapon, in a fixed order. -/
def Weapon.all : List Weapon := [.broadsword, .largeKnife, .punch, .quarterstaff, .flamethrower]

/-- `Weapon.all` lists every weapon. -/
theorem Weapon.mem_all (w : Weapon) : w ∈ Weapon.all := by
  cases w <;> decide

/-- Body armor (p. 18). -/
inductive Armor where
  | none
  | leather
  deriving Repr, DecidableEq

/-- Every type of armor, in a fixed order. -/
def Armor.all : List Armor := [.none, .leather]

/-- `Armor.all` lists every type of armor. -/
theorem Armor.mem_all (a : Armor) : a ∈ Armor.all := by
  cases a <;> decide

/-- The name of a type of armor, for display. -/
def Armor.name : Armor → String
  | .none => "no armor"
  | .leather => "leather armor"

/-- The Damage Resistance (DR) of a type of armor (p. 18). -/
def Armor.dr : Armor → Nat
  | .none => 0
  | .leather => 2

/-- A being: the Character or a Creature. -/
structure Being where
  name : String
  st : Nat
  dx : Nat
  iq : Nat
  ht : Nat
  /-- Each learned skill with its skill level, for example `(.broadsword, 12)`. -/
  skills : List (Skill × Nat)
  weapon : Weapon
  armor : Armor
  /-- Natural DR, such as a stone hide. Only Creatures may have it. -/
  naturalDR : Nat := 0
  deriving Repr, DecidableEq

/-- The score of an attribute. -/
def Being.attr (b : Being) : Attribute → Nat
  | .st => b.st
  | .dx => b.dx
  | .iq => b.iq
  | .ht => b.ht

/-- Hit Points (HP) equal ST (p. 6). -/
def Being.maxHP (b : Being) : Nat := b.st

/-- Total DR: armor plus natural DR. -/
def Being.dr (b : Being) : Nat := b.armor.dr + b.naturalDR

/-- Basic Speed times 4, which is HT + DX (p. 6). It is kept times 4 so that no fractions occur. -/
def Being.speedX4 (b : Being) : Nat := b.ht + b.dx

/-- Dodge is Basic Speed + 3, with fractions dropped (p. 6). -/
def Being.dodge (b : Being) : Nat := b.speedX4 / 4 + 3

/-- The skill level of a learned skill, if the being has learned it. -/
def Being.learnedLevel (b : Being) (s : Skill) : Option Nat :=
  (b.skills.find? (·.1 == s)).map (·.2)

/-- The level at which a being uses a skill: its learned level, or else the default (p. 13).
`none` means it cannot use the skill. -/
def Being.skillLevel (b : Being) (s : Skill) : Option Int :=
  match b.learnedLevel s with
  | some l => some l
  | none => s.defaultPenalty.map fun p => (b.attr s.attribute : Int) + p

/-! ## Point costs -/

/-- Point cost of an attribute score (p. 4): 10 per level for ST and HT, 20 for DX and IQ, from a base of 10. -/
def attributeCost (a : Attribute) (score : Nat) : Int :=
  let perLevel : Int := match a with
    | .st => 10
    | .ht => 10
    | .dx => 20
    | .iq => 20
  perLevel * ((score : Int) - 10)

/-- The lowest skill level you can buy, relative to the attribute: Easy +0, Average -1, Hard -2 (p. 13). -/
def Difficulty.lowestLevel : Difficulty → Int
  | .easy => 0
  | .average => -1
  | .hard => -2

/-- Point cost of a skill by step above the lowest level (Skill Cost Table, p. 13).
Steps 0, 1, 2, 3 cost 1, 2, 4, 8 points. Each further step costs 4 more points. -/
def costOfStep (step : Nat) : Nat :=
  match step with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | n + 3 => 8 + 4 * n

/-- The step of a skill level above the lowest level that can be bought.
`none` means the level is too low to buy. -/
def Being.skillStep (b : Being) (s : Skill) (level : Nat) : Option Nat :=
  let rel : Int := (level : Int) - (b.attr s.attribute : Int)
  let step := rel - s.difficulty.lowestLevel
  if step < 0 then none else some step.toNat

/-- Point cost of one learned skill. A level too low to buy costs 0 here; the spec rejects it. -/
def Being.skillCost (b : Being) (entry : Skill × Nat) : Nat :=
  match b.skillStep entry.1 entry.2 with
  | some step => costOfStep step
  | none => 0

/-- Natural DR costs 5 points per level. This is the price in the full GURPS Basic Set; GURPS Lite has no such trait. -/
def naturalDRCost (dr : Nat) : Int := 5 * dr

/-- Total point cost of a being: attributes, skills, and natural DR. -/
def Being.points (b : Being) : Int :=
  attributeCost .st b.st + attributeCost .dx b.dx + attributeCost .iq b.iq + attributeCost .ht b.ht
    + ((b.skills.map b.skillCost).sum : Nat) + naturalDRCost b.naturalDR

/-! ## Damage -/

/-- A damage roll: a number of six-sided dice plus an add, such as `2d-1`. -/
structure Dice where
  count : Nat
  add : Int
  deriving Repr, DecidableEq

/-- Basic thrust damage by ST, for ST 1 to 20 (Damage Table, p. 6). -/
def thrustTable : List Dice :=
  [⟨1, -6⟩, ⟨1, -6⟩, ⟨1, -5⟩, ⟨1, -5⟩, ⟨1, -4⟩, ⟨1, -4⟩, ⟨1, -3⟩, ⟨1, -3⟩, ⟨1, -2⟩, ⟨1, -2⟩,
   ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨2, -1⟩, ⟨2, -1⟩]

/-- Basic swing damage by ST, for ST 1 to 20 (Damage Table, p. 6). -/
def swingTable : List Dice :=
  [⟨1, -5⟩, ⟨1, -5⟩, ⟨1, -4⟩, ⟨1, -4⟩, ⟨1, -3⟩, ⟨1, -3⟩, ⟨1, -2⟩, ⟨1, -2⟩, ⟨1, -1⟩, ⟨1, 0⟩,
   ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, -1⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨3, -1⟩, ⟨3, 0⟩, ⟨3, 1⟩, ⟨3, 2⟩]

/-- Look up a damage table at a given ST. ST outside 1 to 20 uses the nearest end of the table. -/
def lookupDamage (table : List Dice) (st : Nat) : Dice :=
  table.getD (min (st - 1) 19) ⟨1, -6⟩

/-- Basic thrust damage for a given ST. -/
def thrust (st : Nat) : Dice := lookupDamage thrustTable st

/-- Basic swing damage for a given ST. -/
def swing (st : Nat) : Dice := lookupDamage swingTable st

/-- The skill that a weapon uses. A punch can also use DX (p. 26). -/
def Weapon.skill : Weapon → Skill
  | .broadsword => .broadsword
  | .largeKnife => .knife
  | .punch => .brawling
  | .quarterstaff => .staff
  | .flamethrower => .liquidProjector

/-- The lowest ST that can use a weapon without penalty (p. 20). -/
def Weapon.minST : Weapon → Nat
  | .broadsword => 10
  | .largeKnife => 6
  | .punch => 0
  | .quarterstaff => 7
  | .flamethrower => 10

/-- The damage type of a weapon's attack. -/
def Weapon.damageType : Weapon → DamageType
  | .broadsword => .cutting
  | .largeKnife => .impaling
  | .punch => .crushing
  | .quarterstaff => .crushing
  | .flamethrower => .burning

/-- The damage roll of a weapon in the hands of a being with a given ST. -/
def Weapon.damage (w : Weapon) (st : Nat) : Dice :=
  match w with
  | .broadsword => let d := swing st; ⟨d.count, d.add + 1⟩
  | .largeKnife => thrust st
  | .punch => let d := thrust st; ⟨d.count, d.add - 1⟩
  | .quarterstaff => let d := swing st; ⟨d.count, d.add + 2⟩
  | .flamethrower => ⟨3, 0⟩

/-- The name of a weapon, for display. -/
def Weapon.name : Weapon → String
  | .broadsword => "broadsword"
  | .largeKnife => "large knife"
  | .punch => "fists"
  | .quarterstaff => "quarterstaff"
  | .flamethrower => "flamethrower"

/-- `true` if the weapon attacks every living foe on each turn, not one target. -/
def Weapon.spray : Weapon → Bool
  | .flamethrower => true
  | _ => false

-- A quarterstaff at ST 10 swings for 1d+2: swing damage 1d, plus 2.
#guard Weapon.quarterstaff.damage 10 == ⟨1, 2⟩
-- A Swimming default is HT-4, and a Staff default is DX-5.
#guard Skill.swimming.attribute == .ht && Skill.swimming.defaultPenalty == some (-4)
#guard Skill.staff.defaultPenalty == some (-5)

/-- The lowest basic damage allowed: 0 for crushing, 1 for other types (p. 29). -/
def DamageType.minDamage : DamageType → Nat
  | .crushing => 0
  | _ => 1

/-- Basic damage from the sum of the dice: the add is applied, then the minimum (p. 29). -/
def basicDamage (d : Dice) (t : DamageType) (diceSum : Nat) : Nat :=
  max t.minDamage ((diceSum : Int) + d.add).toNat

/-- Injury from basic damage (p. 29). DR is subtracted first. Then cutting is times 1.5 and
impaling is times 2, with fractions dropped. Any damage that gets past DR gives at least 1 injury. -/
def injury (t : DamageType) (dr : Nat) (basic : Nat) : Nat :=
  let pen := basic - dr
  if pen = 0 then 0 else
  let wounded := match t with
    | .crushing => pen
    | .cutting => pen * 3 / 2
    | .impaling => pen * 2
    | .burning => pen
  max 1 wounded

-- Burning injury is the damage that gets past DR, with no multiplier.
example : injury .burning 2 10 = 8 := by decide
-- The flamethrower does 3d whatever the user's ST.
example : Weapon.flamethrower.damage 11 = ⟨3, 0⟩ := by decide

/-- The level at which a being attacks with its weapon. A punch uses the higher of Brawling and DX (p. 26). -/
def Being.attackLevel (b : Being) : Int :=
  match b.weapon with
  | .punch => max ((b.learnedLevel .brawling).getD 0 : Int) b.dx
  | w => (b.skillLevel w.skill).getD 0

/-! ## Success rolls -/

/-- The result of a success roll (p. 2). -/
inductive RollResult where
  | criticalSuccess
  | success
  | failure
  | criticalFailure
  deriving Repr, DecidableEq

/-- `true` for a success or a critical success. -/
def RollResult.succeeded : RollResult → Bool
  | .criticalSuccess => true
  | .success => true
  | _ => false

/-- The result of a roll of 3d6 (`roll`) against an effective skill (`skill`), by the rules on p. 2.
A roll of 3 or 4 always succeeds, and 17 or 18 always fails. -/
def successRoll (skill : Int) (roll : Nat) : RollResult :=
  let r : Int := roll
  if r ≤ 4 then .criticalSuccess
  else if r = 18 then .criticalFailure
  else if r = 17 then (if skill ≤ 15 then .criticalFailure else .failure)
  else if r ≥ skill + 10 then .criticalFailure
  else if (r = 5 ∧ skill ≥ 15) ∨ (r = 6 ∧ skill ≥ 16) then .criticalSuccess
  else if r ≤ skill then .success
  else .failure

example : successRoll 10 10 = .success := by decide
example : successRoll 10 11 = .failure := by decide
example : successRoll 20 17 = .failure := by decide
example : successRoll 5 15 = .criticalFailure := by decide

/-! ## Maneuvers -/

/-- The maneuvers that a being can choose on its turn in a Fight (p. 25-26).
A maneuver stays in effect for defense until the being chooses again on its next turn. -/
inductive Maneuver where
  /-- Attack, and defend as usual. -/
  | attack
  /-- All-Out Attack (Determined): attack at +4 to hit, with no defense until the next turn. -/
  | allOutAttack
  /-- All-Out Defense (Increased Defense): do not attack, and get +2 to Dodge until the next turn. -/
  | allOutDefense
  deriving Repr, DecidableEq

/-- `true` if the maneuver includes an attack. -/
def Maneuver.attacks : Maneuver → Bool
  | .allOutDefense => false
  | _ => true

/-- The bonus to the attack roll: +4 for All-Out Attack (Determined), else 0. -/
def Maneuver.hitBonus : Maneuver → Int
  | .allOutAttack => 4
  | _ => 0

/-- The bonus to Dodge, or `none` if the being cannot defend.
All-Out Attack gives no defense, and All-Out Defense gives +2. -/
def Maneuver.dodgeBonus : Maneuver → Option Nat
  | .attack => some 0
  | .allOutAttack => none
  | .allOutDefense => some 2

/-- The name and effect of a maneuver, for display. -/
def Maneuver.describe : Maneuver → String
  | .attack => "Attack"
  | .allOutAttack => "All-Out Attack: +4 to hit, but no Dodge until the next turn"
  | .allOutDefense => "All-Out Defense: no attack, but +2 to Dodge until the next turn"

example : Maneuver.allOutAttack.hitBonus = 4 := by decide
example : Maneuver.allOutAttack.dodgeBonus = none := by decide
example : Maneuver.allOutDefense.attacks = false := by decide

end Rpg
