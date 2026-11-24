import MarkovRPGMainTypes
import MarkovRPGRules
import Mathlib.Tactic

/-!
# Complete characters, items, and their combat views

Human-controlled characters and NPCs share these types. The action-selection
policy belongs to the graph, not to the character. Main's ST/DX/IQ/HT, skill
defaults, weapon damage, armor DR, and maneuver meanings are preserved.

Equipment references inventory entries by ID. Item mechanics and presentation
are separated to permit a combat projection that forgets names, but no mechanical
information. Further reductions require the projection theorem in
`MarkovRPGCharacterGraph`. Effects describe operations; this file does not invent
a new combat resolution order or a probability law for dice.
-/

namespace MarkovRPG

open MainRules

structure CharacterId where
  value : Nat
  deriving Repr, DecidableEq

structure ItemId where
  value : Nat
  deriving Repr, DecidableEq

structure ResourceId where
  value : Nat
  deriving Repr, DecidableEq

/-- Main's character statistics, without presentation or duplicated equipment. -/
structure Statistics where
  st : Nat
  dx : Nat
  iq : Nat
  ht : Nat
  skills : List (Skill × Nat)
  naturalDR : Nat := 0
  deriving Repr, DecidableEq

def Statistics.ofBeing (b : Being) : Statistics :=
  ⟨b.st, b.dx, b.iq, b.ht, b.skills, b.naturalDR⟩

def Statistics.toBeing (s : Statistics) (name : String) (weapon : Weapon)
    (armor : Armor) : Being :=
  ⟨name, s.st, s.dx, s.iq, s.ht, s.skills, weapon, armor, s.naturalDR⟩

/-- Structural validity, independently of character-creation point budgets. -/
def Statistics.WellFormed (s : Statistics) : Prop :=
  0 < s.st ∧ (s.skills.map Prod.fst).Nodup

instance (s : Statistics) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable (0 < s.st ∧ (s.skills.map Prod.fst).Nodup))

/-- An effect recipient is relative to the actor, including when the actor is an NPC.
Main's flamethrower requires the third case. -/
inductive EffectTarget where
  | self
  | opponent
  | allOpponents
  deriving Repr, DecidableEq

/-- Typed property names prevent confusing HP, attributes, skills, and resources. -/
inductive CharacterProperty where
  | health
  | attribute (key : Attribute)
  | skill (key : Skill)
  | protection
  | resource (key : ResourceId)
  deriving Repr, DecidableEq

/-- Default usage in the present rulebook. These are overlapping masks on
property names, not tests on the numeric value of an entire character. -/
def CharacterProperty.isCombat : CharacterProperty → Bool
  | .health | .protection | .resource _ => true
  | .attribute .st | .attribute .dx | .attribute .ht => true
  | .attribute .iq => false
  | .skill .broadsword | .skill .knife | .skill .brawling
  | .skill .staff | .skill .liquidProjector => true
  | .skill _ => false

def CharacterProperty.isAdventure : CharacterProperty → Bool
  | .health | .attribute _ | .resource _ => true
  | .protection => false
  | .skill .broadsword | .skill .knife | .skill .brawling
  | .skill .staff | .skill .liquidProjector => false
  | .skill _ => true

/-- A game can declare further dependencies, for example sword proficiency in
an intimidation event. Masks alone are not a proof that a kernel ignores data. -/
structure PropertyUsage where
  combat : CharacterProperty → Bool := CharacterProperty.isCombat
  adventure : CharacterProperty → Bool := CharacterProperty.isAdventure

def Statistics.value (s : Statistics) : CharacterProperty → Option Nat
  | .attribute .st => some s.st
  | .attribute .dx => some s.dx
  | .attribute .iq => some s.iq
  | .attribute .ht => some s.ht
  | .skill k => ((s.skills.find? (fun e => e.1 == k)).map Prod.snd)
  | .protection => some s.naturalDR
  | .health | .resource _ => none

/-- An absent skill is kept distinct from a learned skill of level zero. -/
def Statistics.project (s : Statistics) (mask : CharacterProperty → Bool)
    (key : CharacterProperty) : Option Nat :=
  if mask key then s.value key else none

def Statistics.combatView (s : Statistics) (usage : PropertyUsage := {}) :=
  s.project usage.combat

def Statistics.adventureView (s : Statistics) (usage : PropertyUsage := {}) :=
  s.project usage.adventure

@[simp] theorem Statistics.project_included (s : Statistics) (mask : CharacterProperty → Bool)
    (key : CharacterProperty) (h : mask key = true) :
    s.project mask key = s.value key := by simp [project, h]

@[simp] theorem Statistics.project_excluded (s : Statistics) (mask : CharacterProperty → Bool)
    (key : CharacterProperty) (h : mask key = false) :
    s.project mask key = none := by simp [project, h]

/-- A shared property has the identical original value in both views. -/
theorem Statistics.shared_views (s : Statistics) (usage : PropertyUsage)
    (key : CharacterProperty) (hc : usage.combat key = true)
    (ha : usage.adventure key = true) :
    s.combatView usage key = s.adventureView usage key := by
  simp [combatView, adventureView, project, hc, ha]

/-- HP and resources belong to CharacterState, not its base Statistics record. -/
def CharacterProperty.isStoredStatistic : CharacterProperty → Bool
  | .attribute _ | .skill _ | .protection => true
  | _ => false

/-- Set one base statistic. Unsupported state fields are rejected by the rule
change checker. Replacing a learned skill removes any previous entry for it. -/
def Statistics.set (s : Statistics) (key : CharacterProperty) (value : Nat) : Statistics :=
  match key with
  | .attribute .st => { s with st := value }
  | .attribute .dx => { s with dx := value }
  | .attribute .iq => { s with iq := value }
  | .attribute .ht => { s with ht := value }
  | .protection => { s with naturalDR := value }
  | .skill k => { s with skills := (k, value) :: s.skills.filter (fun e => e.1 != k) }
  | _ => s

theorem Statistics.set_value (s : Statistics) (key : CharacterProperty) (n : Nat)
    (h : key.isStoredStatistic = true) : (s.set key n).value key = some n := by
  cases key with
  | health => simp [CharacterProperty.isStoredStatistic] at h
  | resource id => simp [CharacterProperty.isStoredStatistic] at h
  | «attribute» a => cases a <;> rfl
  | protection => rfl
  | skill k => simp [set, value]

/-- Persistent modifiers do not repeatedly inflict damage or healing. -/
inductive Modifier where
  | attribute (key : Attribute) (delta : Int)
  | skill (key : Skill) (delta : Int)
  | protection (delta : Int)
  | resource (key : ResourceId) (delta : Int)
  deriving Repr, DecidableEq

def Modifier.property : Modifier → CharacterProperty
  | .attribute key _ => .attribute key
  | .skill key _ => .skill key
  | .protection _ => .protection
  | .resource key _ => .resource key

/-- Weapons use exactly main's ST-dependent damage descriptions. A roll is a
description here; the combat kernel will supply its random outcome. -/
inductive DamageSpec where
  | fixed (amount : Nat) (kind : DamageType)
  | roll (dice : Dice) (kind : DamageType)
  | weapon (kind : Weapon)
  deriving Repr, DecidableEq

def DamageSpec.damageType : DamageSpec → DamageType
  | .fixed _ kind | .roll _ kind => kind
  | .weapon kind => kind.damageType

/-- Basic damage before protection and the injury multiplier. -/
def DamageSpec.basic (d : DamageSpec) (strength diceSum : Nat) : Nat :=
  match d with
  | .fixed amount _ => amount
  | .roll dice kind => MainRules.basicDamage dice kind diceSum
  | .weapon w => MainRules.basicDamage (w.damage strength) w.damageType diceSum

def DamageSpec.injury (d : DamageSpec) (strength diceSum protection : Nat) : Nat :=
  MainRules.injury d.damageType protection (d.basic strength diceSum)

inductive ImmediateEffect where
  | damage (description : DamageSpec)
  | heal (amount : Nat)
  deriving Repr, DecidableEq

/-- The constructors encode activation and duration: passive equipment bonuses
are modifiers, and timed modifiers have a strictly positive lifetime. -/
inductive ItemEffect where
  | onUse (target : EffectTarget) (operation : ImmediateEffect)
  | onHit (target : EffectTarget) (damage : DamageSpec)
  | whileEquipped (modifier : Modifier)
  | timedOnUse (target : EffectTarget) (modifier : Modifier)
      (turns : {n : Nat // 0 < n})
  deriving Repr, DecidableEq

def ItemEffect.target : ItemEffect → EffectTarget
  | .onUse target _ | .onHit target _ | .timedOnUse target _ _ => target
  | .whileEquipped _ => .self

/-- The affected property is derived from the operation, so the two cannot disagree. -/
def ItemEffect.property : ItemEffect → CharacterProperty
  | .onUse _ _ | .onHit _ _ => .health
  | .whileEquipped modifier | .timedOnUse _ modifier _ => modifier.property

inductive ItemKind where
  | weapon (kind : Weapon)
  | armor (kind : Armor)
  | consumable
  | reusable
  deriving Repr, DecidableEq

inductive UsageMode where
  | consumable
  | reusable
  | equipped
  deriving Repr, DecidableEq

/-- Gameplay data for an item. Canonical weapon/armor effects are derived from
`kind`; `additionalEffects` is for explicitly added effects. -/
structure ItemMechanics where
  id : ItemId
  kind : ItemKind
  additionalEffects : List ItemEffect := []
  deriving Repr, DecidableEq

/-- The complete item object, including its presentation. -/
structure Item extends ItemMechanics where
  name : String
  deriving Repr, DecidableEq

def ItemMechanics.usage (i : ItemMechanics) : UsageMode :=
  match i.kind with
  | .consumable => .consumable
  | .armor _ => .equipped
  | _ => .reusable

def ItemMechanics.baseEffects (i : ItemMechanics) : List ItemEffect :=
  match i.kind with
  | .weapon w => [.onHit (if w.spray then .allOpponents else .opponent) (.weapon w)]
  | .armor a => [.whileEquipped (.protection (a.dr : Int))]
  | _ => []

def ItemMechanics.effects (i : ItemMechanics) : List ItemEffect :=
  i.baseEffects ++ i.additionalEffects

def Item.weapon (id : ItemId) (w : Weapon) : Item :=
  ⟨⟨id, .weapon w, []⟩, w.name⟩

def Item.armor (id : ItemId) (a : Armor) : Item :=
  ⟨⟨id, .armor a, []⟩, a.name⟩

def Item.healingPotion (id : ItemId) (name : String) (amount : Nat) : Item :=
  ⟨⟨id, .consumable, [.onUse .self (.heal amount)]⟩, name⟩

@[simp] theorem weapon_affects_health (id : ItemId) (w : Weapon) :
    ((Item.weapon id w).toItemMechanics.effects.map ItemEffect.property) = [.health] := by
  simp [Item.weapon, ItemMechanics.effects, ItemMechanics.baseEffects, ItemEffect.property]

@[simp] theorem armor_affects_protection (id : ItemId) (a : Armor) :
    ((Item.armor id a).toItemMechanics.effects.map ItemEffect.property) = [.protection] := by
  simp [Item.armor, ItemMechanics.effects, ItemMechanics.baseEffects,
    ItemEffect.property, Modifier.property]

@[simp] theorem potion_effect (id : ItemId) (name : String) (amount : Nat) :
    (Item.healingPotion id name amount).toItemMechanics.effects =
      [.onUse .self (.heal amount)] := rfl

/-- Inventory IDs identify stacks; quantity is the number of available instances. -/
structure InventoryEntry where
  item : Item
  quantity : Nat
  deriving Repr, DecidableEq

structure CombatInventoryEntry where
  item : ItemMechanics
  quantity : Nat
  deriving Repr, DecidableEq

def InventoryEntry.toCombat (e : InventoryEntry) : CombatInventoryEntry :=
  ⟨e.item.toItemMechanics, e.quantity⟩

/-- No second copy of the equipped item or its statistics is stored. -/
structure Equipment where
  weapon : Option ItemId := none
  armor : Option ItemId := none
  deriving Repr, DecidableEq

def findItem (inventory : List CombatInventoryEntry) (id : ItemId) : Option ItemMechanics :=
  (inventory.find? (fun e => e.item.id == id)).map (·.item)

def Equipment.weaponKind (e : Equipment) (inventory : List CombatInventoryEntry) : Weapon :=
  match e.weapon.bind (findItem inventory) with
  | some ⟨_, .weapon w, _⟩ => w
  | _ => .punch

def Equipment.armorKind (e : Equipment) (inventory : List CombatInventoryEntry) : Armor :=
  match e.armor.bind (findItem inventory) with
  | some ⟨_, .armor a, _⟩ => a
  | _ => .none

/-- Dangling references and slot/type mismatches are invalid, rather than legal
uses of the fallback values of the total lookup functions. -/
def Equipment.validSlot (slot : Option ItemId) (accepts : ItemKind → Bool)
    (inventory : List CombatInventoryEntry) : Bool :=
  match slot with
  | none => true
  | some id => ((findItem inventory id).map (fun i => accepts i.kind)).getD false

def Equipment.WellFormed (e : Equipment) (inventory : List CombatInventoryEntry) : Prop :=
  Equipment.validSlot e.weapon (fun kind => match kind with | .weapon _ => true | _ => false)
    inventory = true ∧
  Equipment.validSlot e.armor (fun kind => match kind with | .armor _ => true | _ => false)
    inventory = true

instance (e : Equipment) (inventory : List CombatInventoryEntry) :
    Decidable (e.WellFormed inventory) := by
  unfold Equipment.WellFormed
  infer_instance

/-- The full character object. Current HP and timed effects live in its state. -/
structure Character where
  id : CharacterId
  name : String
  statistics : Statistics
  inventory : List InventoryEntry
  equipment : Equipment
  deriving Repr, DecidableEq

def Character.combatInventory (c : Character) : List CombatInventoryEntry :=
  c.inventory.map InventoryEntry.toCombat

def Character.toBeing (c : Character) : Being :=
  c.statistics.toBeing c.name (c.equipment.weaponKind c.combatInventory)
    (c.equipment.armorKind c.combatInventory)

/-- A lossless adapter for main's Being. The two legacy equipment slots become
inventory entries 0 and 1, including the inert `punch`/`none` defaults. -/
def Character.ofBeing (id : CharacterId) (b : Being) : Character :=
  ⟨id, b.name, .ofBeing b,
    [⟨.weapon ⟨0⟩ b.weapon, 1⟩, ⟨.armor ⟨1⟩ b.armor, 1⟩],
    ⟨some ⟨0⟩, some ⟨1⟩⟩⟩

@[simp] theorem Character.toBeing_ofBeing (id : CharacterId) (b : Being) :
    (Character.ofBeing id b).toBeing = b := by
  cases b
  simp [Character.ofBeing, Character.toBeing, Character.combatInventory,
    InventoryEntry.toCombat, Statistics.ofBeing, Statistics.toBeing,
    Equipment.weaponKind, Equipment.armorKind, findItem, Item.weapon, Item.armor]

/-- A timed modifier is already attached to its recipient. Its remaining lifetime
is part of the state, so it does not hide history outside the Markov state. -/
structure ActiveEffect where
  modifier : Modifier
  remaining : {n : Nat // 0 < n}
  deriving Repr, DecidableEq

structure CharacterState where
  character : Character
  hp : Int
  effects : List ActiveEffect := []
  resources : List (ResourceId × Nat) := []
  deriving Repr, DecidableEq

/-- A conservative sufficient combat view. Names are omitted; all statistics,
skills, item mechanics, quantities, equipment, effects, and resources remain.
An engine using a smaller view must certify that reduction separately. -/
structure CharacterStateCombat where
  id : CharacterId
  statistics : Statistics
  inventory : List CombatInventoryEntry
  equipment : Equipment
  hp : Int
  effects : List ActiveEffect
  resources : List (ResourceId × Nat)
  deriving Repr, DecidableEq

def CharacterState.toCombat (s : CharacterState) : CharacterStateCombat :=
  ⟨s.character.id, s.character.statistics, s.character.combatInventory,
    s.character.equipment, s.hp, s.effects, s.resources⟩

/-- Full-state views also expose current HP and resources, without copying or
resetting them. The sufficient combat snapshot above deliberately stays intact. -/
def CharacterState.propertyValue (s : CharacterState) : CharacterProperty → Option Int
  | .health => some s.hp
  | .resource id => ((s.resources.find? (fun e => e.1 == id)).map (fun e => (e.2 : Int)))
  | key => (s.character.statistics.value key).map Int.ofNat

def CharacterState.combatView (s : CharacterState) (usage : PropertyUsage := {})
    (key : CharacterProperty) : Option Int :=
  if usage.combat key then s.propertyValue key else none

def CharacterState.adventureView (s : CharacterState) (usage : PropertyUsage := {})
    (key : CharacterProperty) : Option Int :=
  if usage.adventure key then s.propertyValue key else none

theorem CharacterState.shared_views (s : CharacterState) (usage : PropertyUsage)
    (key : CharacterProperty) (hc : usage.combat key = true)
    (ha : usage.adventure key = true) :
    s.combatView usage key = s.adventureView usage key := by
  simp [combatView, adventureView, hc, ha]

def CharacterStateCombat.toBeing (s : CharacterStateCombat) (name : String) : Being :=
  s.statistics.toBeing name (s.equipment.weaponKind s.inventory)
    (s.equipment.armorKind s.inventory)

@[simp] theorem CharacterState.toCombat_toBeing (s : CharacterState) :
    s.toCombat.toBeing s.character.name = s.character.toBeing := rfl

/-- Alive means strictly positive HP; validity separately requires nonnegative HP. -/
def CharacterState.alive (s : CharacterState) : Prop := 0 < s.hp

def CharacterStateCombat.alive (s : CharacterStateCombat) : Prop := 0 < s.hp

@[simp] theorem CharacterState.toCombat_alive (s : CharacterState) :
    s.toCombat.alive ↔ s.alive := Iff.rfl

namespace Combat

def Modifier.amount : Modifier → Int
  | .attribute _ n | .skill _ n | .protection n | .resource _ n => n

def Modifier.Bounded (r : Rules) (m : Modifier) : Prop := (Modifier.amount m).natAbs ≤ r.modifierMax

def DamageSpec.Bounded (r : Rules) : DamageSpec → Prop
  | .fixed amount _ => amount ≤ r.damageMax
  | .roll dice _ => dice.count ≤ r.diceMax ∧ dice.add.natAbs ≤ r.modifierMax
  | .weapon w => ∀ st ∈ List.range (r.attributeMax + 1),
      (w.damage st).count ≤ r.diceMax ∧ (w.damage st).add.natAbs ≤ r.modifierMax

def ItemEffect.Bounded (r : Rules) : ItemEffect → Prop
  | .onUse _ (.damage d) | .onHit _ d => DamageSpec.Bounded r d
  | .onUse _ (.heal n) => n ≤ r.hpMax
  | .whileEquipped m => Modifier.Bounded r m
  | .timedOnUse _ m n => Modifier.Bounded r m ∧ n.val ≤ r.durationMax

instance (r : Rules) (m : Modifier) : Decidable (Modifier.Bounded r m) :=
  inferInstanceAs (Decidable ((Modifier.amount m).natAbs ≤ r.modifierMax))

instance (r : Rules) (d : DamageSpec) : Decidable (DamageSpec.Bounded r d) := by
  cases d <;> unfold DamageSpec.Bounded <;> infer_instance

instance (r : Rules) (e : ItemEffect) : Decidable (ItemEffect.Bounded r e) := by
  cases e with
  | onUse t op => cases op <;> unfold ItemEffect.Bounded <;> infer_instance
  | onHit => unfold ItemEffect.Bounded; infer_instance
  | whileEquipped => unfold ItemEffect.Bounded; infer_instance
  | timedOnUse => unfold ItemEffect.Bounded; infer_instance

end Combat

open Combat in
/-- A single global rulebook bounds adventure and combat character snapshots.
Base statistics are independent of temporary modifiers; HP is independent of ST. -/
def CharacterStateCombat.WellFormed (c : CharacterStateCombat) (r : Combat.Rules) : Prop :=
  c.statistics.WellFormed ∧
  c.statistics.st ≤ r.attributeMax ∧ c.statistics.dx ≤ r.attributeMax ∧
  c.statistics.iq ≤ r.attributeMax ∧ c.statistics.ht ≤ r.attributeMax ∧
  c.statistics.naturalDR ≤ r.protectionMax ∧
  (∀ entry ∈ c.statistics.skills, entry.2 ≤ r.skillMax) ∧
  0 ≤ c.hp ∧ c.hp ≤ (r.hpMax : Int) ∧
  c.inventory.length ≤ r.itemSlots ∧
  (c.inventory.map (fun e => e.item.id)).Nodup ∧
  (∀ e ∈ c.inventory, 0 < e.quantity ∧ e.quantity ≤ r.stockMax ∧
    e.item.effects.length ≤ r.effectsPerSource ∧
    ∀ effect ∈ e.item.effects, ItemEffect.Bounded r effect) ∧
  c.equipment.WellFormed c.inventory ∧
  DamageSpec.Bounded r (.weapon (c.equipment.weaponKind c.inventory)) ∧
  c.effects.length ≤ r.effectsPerSource ∧
  (∀ e ∈ c.effects, Modifier.Bounded r e.modifier ∧ e.remaining.val ≤ r.durationMax) ∧
  (c.resources.map Prod.fst).Nodup ∧
  (∀ e ∈ c.resources, e.2 ≤ r.resourceMax)

instance (s : CharacterStateCombat) (r : Combat.Rules) : Decidable (s.WellFormed r) := by
  unfold CharacterStateCombat.WellFormed
  infer_instance

def CharacterState.WellFormed (s : CharacterState) (r : Combat.Rules) : Prop :=
  s.toCombat.WellFormed r

instance (s : CharacterState) (r : Combat.Rules) : Decidable (s.WellFormed r) :=
  inferInstanceAs (Decidable (s.toCombat.WellFormed r))

def CharacterState.check (s : CharacterState) (r : Combat.Rules) : Bool :=
  decide (s.WellFormed r)

@[simp] theorem CharacterState.check_eq_true (s : CharacterState) (r : Combat.Rules) :
    s.check r = true ↔ s.WellFormed r := by simp [check]

@[simp] theorem CharacterState.toCombat_wellFormed (s : CharacterState) (r : Combat.Rules) :
    s.toCombat.WellFormed r ↔ s.WellFormed r := Iff.rfl

/-- HP saturates at zero, exactly as in the finite combat graph. -/
def CharacterStateCombat.takeDamage (s : CharacterStateCombat) (amount : Nat) :
    CharacterStateCombat := { s with hp := max 0 (s.hp - amount) }

/-- Healing uses the shared HP cap, never ST. -/
def CharacterStateCombat.heal (s : CharacterStateCombat) (r : Combat.Rules) (amount : Nat) :
    CharacterStateCombat := { s with hp := min (s.hp + amount) (r.hpMax : Int) }

/-- Replacing HP within the shared bounds preserves every other input invariant. -/
theorem CharacterStateCombat.withHP_wellFormed (s : CharacterStateCombat) (r : Combat.Rules)
    (hs : s.WellFormed r) (hp : Int) (lower : 0 ≤ hp) (upper : hp ≤ r.hpMax) :
    ({s with hp := hp} : CharacterStateCombat).WellFormed r := by
  simp only [WellFormed] at *
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, lower, upper, hs.2.2.2.2.2.2.2.2.2⟩

theorem CharacterStateCombat.takeDamage_wellFormed (s : CharacterStateCombat)
    (r : Combat.Rules) (hs : s.WellFormed r) (amount : Nat) :
    (s.takeDamage amount).WellFormed r := by
  apply s.withHP_wellFormed r hs
  · exact le_max_left _ _
  · have h := hs
    simp only [WellFormed] at h
    have hr := r.hpMax_pos
    omega

theorem CharacterStateCombat.heal_wellFormed (s : CharacterStateCombat)
    (r : Combat.Rules) (hs : s.WellFormed r) (amount : Nat) :
    (s.heal r amount).WellFormed r := by
  apply s.withHP_wellFormed r hs
  · have h := hs
    simp only [WellFormed] at h
    omega
  · exact min_le_right _ _

theorem CharacterStateCombat.heal_non_decreasing (s : CharacterStateCombat)
    (r : Combat.Rules) (hs : s.WellFormed r) (amount : Nat) : s.hp ≤ (s.heal r amount).hp := by
  have h := hs
  simp only [WellFormed] at h
  dsimp [heal]
  omega

/-- Spending one unit of a stack fails for an empty stack. A zero remainder is
returned explicitly; an inventory update must remove it and repair equipment. -/
def CombatInventoryEntry.spendOne (e : CombatInventoryEntry) : Option CombatInventoryEntry :=
  if e.quantity = 0 then none else some { e with quantity := e.quantity - 1 }

theorem CombatInventoryEntry.spendOne_spec (e result : CombatInventoryEntry)
    (h : e.spendOne = some result) :
    result.item = e.item ∧ result.quantity + 1 = e.quantity := by
  unfold spendOne at h
  split at h
  · simp at h
  · cases Option.some.inj h
    exact ⟨rfl, by dsimp; omega⟩

/-- Only a consumable may be spent by the consumable-use operation. -/
def CombatInventoryEntry.consume (e : CombatInventoryEntry) : Option CombatInventoryEntry :=
  if e.item.usage = .consumable then e.spendOne else none

theorem CombatInventoryEntry.consume_spec (e result : CombatInventoryEntry)
    (h : e.consume = some result) :
    e.item.usage = .consumable ∧ result.item = e.item ∧
      result.quantity + 1 = e.quantity := by
  unfold consume at h
  split at h
  · exact ⟨‹_›, e.spendOne_spec result h⟩
  · simp at h

/-- Presentation is supplied explicitly on return, including for newly acquired
items. Thus combat may add/remove items without inventing their display names. -/
def CharacterStateCombat.restore (s : CharacterStateCombat) (characterName : String)
    (itemName : ItemId → String) : CharacterState :=
  ⟨⟨s.id, characterName, s.statistics,
    s.inventory.map (fun e => ⟨⟨e.item, itemName e.item.id⟩, e.quantity⟩), s.equipment⟩,
    s.hp, s.effects, s.resources⟩

/-- Reattaching presentation loses no combat information, including quantities
and persistent modifications made during the fight. -/
@[simp] theorem CharacterStateCombat.toCombat_restore (s : CharacterStateCombat)
    (characterName : String) (itemName : ItemId → String) :
    (s.restore characterName itemName).toCombat = s := by
  cases s
  simp [restore, CharacterState.toCombat, Character.combatInventory,
    InventoryEntry.toCombat, List.map_map, Function.comp_def]

/-- The reverse round trip is exact when the supplied names match the original
items. The premise concerns presentation only; no gameplay equality is assumed. -/
theorem CharacterState.restore_toCombat (s : CharacterState) (itemName : ItemId → String)
    (hnames : ∀ e ∈ s.character.inventory, itemName e.item.id = e.item.name) :
    s.toCombat.restore s.character.name itemName = s := by
  have hinv : s.character.inventory.map
      (fun e => (⟨⟨e.item.toItemMechanics, itemName e.item.id⟩, e.quantity⟩ : InventoryEntry)) =
        s.character.inventory := by
    conv_rhs => rw [← List.map_id s.character.inventory]
    apply List.map_congr_left
    intro e he
    rw [hnames e he]
    rfl
  cases s with
  | mk character hp effects resources =>
    cases character
    simp_all [toCombat, CharacterStateCombat.restore, Character.combatInventory,
      InventoryEntry.toCombat, List.map_map, Function.comp_def]

theorem CharacterStateCombat.restore_wellFormed (s : CharacterStateCombat) (r : Combat.Rules)
    (characterName : String) (itemName : ItemId → String) :
    (s.restore characterName itemName).WellFormed r ↔ s.WellFormed r := by
  simp [CharacterState.WellFormed]

/-- A return is accepted only for the same character and a valid resulting state.
The caller supplies proofs rather than silently repairing invalid combat output. -/
def CharacterState.applyCombatResult (r : Combat.Rules) (original : CharacterState)
    (result : CharacterStateCombat) (itemName : ItemId → String)
    (_sameCharacter : result.id = original.character.id)
    (_valid : result.WellFormed r) : CharacterState :=
  result.restore original.character.name itemName

theorem CharacterState.applyCombatResult_valid (r : Combat.Rules) (original : CharacterState)
    (result : CharacterStateCombat) (itemName : ItemId → String)
    (hid : result.id = original.character.id) (hv : result.WellFormed r) :
    (original.applyCombatResult r result itemName hid hv).WellFormed r := by
  simpa [applyCombatResult] using
    (result.restore_wellFormed r original.character.name itemName).mpr hv

@[simp] theorem CharacterState.applyCombatResult_id (r : Combat.Rules) (original : CharacterState)
    (result : CharacterStateCombat) (itemName : ItemId → String)
    (hid : result.id = original.character.id) (hv : result.WellFormed r) :
    (original.applyCombatResult r result itemName hid hv).character.id =
      original.character.id := hid

@[simp] theorem CharacterState.applyCombatResult_name (r : Combat.Rules) (original : CharacterState)
    (result : CharacterStateCombat) (itemName : ItemId → String)
    (hid : result.id = original.character.id) (hv : result.WellFormed r) :
    (original.applyCombatResult r result itemName hid hv).character.name =
      original.character.name := rfl

@[simp] theorem CharacterState.applyCombatResult_project (r : Combat.Rules) (original : CharacterState)
    (result : CharacterStateCombat) (itemName : ItemId → String)
    (hid : result.id = original.character.id) (hv : result.WellFormed r) :
    (original.applyCombatResult r result itemName hid hv).toCombat = result := by
  simp [applyCombatResult]

/-- A full main-graph state contains scene and character states, not just a scene
ID. `World` must include other variables used by the adventure's transition law. -/
structure GameState (Scene World : Type*) where
  scene : Scene
  hero : CharacterState
  npcs : List CharacterState
  world : World

/-- Global identity uniqueness is a world invariant, not a restriction on whether
a character is player-controlled or an NPC. -/
def GameState.WellFormed {Scene World : Type*} (s : GameState Scene World) (r : Combat.Rules) : Prop :=
  s.hero.WellFormed r ∧ (∀ c ∈ s.npcs, c.WellFormed r) ∧
  (s.hero.character.id :: s.npcs.map (fun c => c.character.id)).Nodup

/-- Combat retains all participants and their last maneuvers. `Context` holds
the phase, pending roll, targets, and any other data used by a concrete kernel.
Multiple foes are supported, as in main. -/
structure CombatState (n : Nat) (Context : Type*) where
  participants : Fin n → CharacterStateCombat
  currentActor : Fin n
  maneuvers : Fin n → Maneuver
  context : Context

def CombatState.WellFormed {n : Nat} {Context : Type*} (s : CombatState n Context) (r : Combat.Rules) : Prop :=
  (∀ i, (s.participants i).WellFormed r) ∧
    Function.Injective (fun i => (s.participants i).id)

end MarkovRPG
