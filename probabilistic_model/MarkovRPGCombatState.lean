import MarkovRPGCharacters
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# A globally bounded state space shared by all duels

Rules are fixed before characters are created. HP is bounded by the common
`hpMax`, independently of ST. Character records are static inputs; the graph
stores only HP, turn, defense, stocks, and remaining effect lifetimes.

Temporary effects are indexed by their source. Reusing the same source refreshes
its lifetime; distinct sources stack. All counters are bounded by construction.
Item/effect IDs and names remain in the static input and do not enlarge the graph.
-/

namespace MarkovRPG.Combat

set_option backward.isDefEq.respectTransparency false

open MainRules

inductive Player where
  | A
  | B
  deriving DecidableEq, Repr, Fintype

def Player.other : Player → Player
  | .A => .B
  | .B => .A

@[simp] theorem Player.other_other (p : Player) : p.other.other = p := by cases p <;> rfl
@[simp] theorem Player.other_ne (p : Player) : p.other ≠ p := by cases p <;> decide

/-- Outcomes are relative to player A. Final HP and stocks remain available. -/
inductive Outcome where
  | Win
  | Lose
  deriving DecidableEq, Repr, Fintype

/-- A stable slot for each initially active effect or item effect. -/
inductive EffectKey (r : Rules) where
  | initial (owner : Player) (slot : Fin r.effectsPerSource)
  | item (owner : Player) (item : Fin r.itemSlots) (slot : Fin r.effectsPerSource)
  deriving DecidableEq, Fintype

/-- Stock and timer functions are finite arrays, not unbounded histories.
`guarded` describes the OTHER player, who is waiting for the current actor.
The actor's previous defense expires when that actor chooses its new action. -/
structure Vertex (r : Rules) where
  turn : Player
  hp : Player → Fin (r.hpMax + 1)
  guarded : Bool
  stock : Player → Fin r.itemSlots → Fin (r.stockMax + 1)
  remaining : Player → EffectKey r → Fin (r.durationMax + 1)
  deriving DecidableEq

def Vertex.equiv (r : Rules) : Vertex r ≃
    Player × (Player → Fin (r.hpMax + 1)) × Bool ×
      (Player → Fin r.itemSlots → Fin (r.stockMax + 1)) ×
      (Player → EffectKey r → Fin (r.durationMax + 1)) where
  toFun s := ⟨s.turn, s.hp, s.guarded, s.stock, s.remaining⟩
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (r : Rules) : Fintype (Vertex r) := Fintype.ofEquiv _ (Vertex.equiv r).symm

def clamp (bound value : Nat) : Fin (bound + 1) :=
  ⟨min value bound, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

@[simp] theorem clamp_val (bound value : Nat) : (clamp bound value).val = min value bound := rfl

/-- Losing takes priority if both participants are dead. This is an explicit
two-output convention, including for self-damaging items. -/
def Vertex.output {r : Rules} (s : Vertex r) : Option Outcome :=
  if (s.hp .A).val = 0 then some .Lose
  else if (s.hp .B).val = 0 then some .Win
  else none

theorem Vertex.output_none_iff {r : Rules} (s : Vertex r) :
    s.output = none ↔ 0 < (s.hp .A).val ∧ 0 < (s.hp .B).val := by
  by_cases ha : (s.hp .A).val = 0 <;> by_cases hb : (s.hp .B).val = 0 <;>
    simp [output, ha, hb, Nat.pos_iff_ne_zero]

theorem Vertex.output_lose_iff {r : Rules} (s : Vertex r) :
    s.output = some .Lose ↔ (s.hp .A).val = 0 := by
  simp [output]

theorem Vertex.output_win_iff {r : Rules} (s : Vertex r) :
    s.output = some .Win ↔ 0 < (s.hp .A).val ∧ (s.hp .B).val = 0 := by
  by_cases ha : (s.hp .A).val = 0 <;> by_cases hb : (s.hp .B).val = 0 <;>
    simp [output, ha, hb, Nat.pos_iff_ne_zero]

theorem Vertex.outputs_disjoint {r : Rules} (s : Vertex r) :
    ¬ (s.output = some .Win ∧ s.output = some .Lose) := by
  rintro ⟨hw, hl⟩
  rw [hw] at hl
  contradiction

theorem Vertex.hp_bounded {r : Rules} (s : Vertex r) (p : Player) :
    (s.hp p).val ≤ r.hpMax := Nat.le_of_lt_succ (s.hp p).isLt

/-- The requested signed coordinate is a bounded cumulative difference, not an
unbounded sum of injuries and heals. -/
def Vertex.delta {r : Rules} (initial s : Vertex r) (p : Player) : Int :=
  ((s.hp p).val : Int) - (initial.hp p).val

theorem Vertex.delta_bounds {r : Rules} (initial s : Vertex r) (p : Player) :
    -((initial.hp p).val : Int) ≤ initial.delta s p ∧
      initial.delta s p ≤ (r.hpMax : Int) - (initial.hp p).val := by
  have h := s.hp_bounded p
  dsimp [delta]
  omega

def Vertex.hurt {r : Rules} (s : Vertex r) (p : Player) (amount : Nat) : Vertex r :=
  { s with hp := Function.update s.hp p (clamp r.hpMax ((s.hp p).val - amount)) }

def Vertex.heal {r : Rules} (s : Vertex r) (p : Player) (amount : Nat) : Vertex r :=
  { s with hp := Function.update s.hp p (clamp r.hpMax ((s.hp p).val + amount)) }

theorem Vertex.hurt_hp {r : Rules} (s : Vertex r) (p : Player) (amount : Nat) :
    ((s.hurt p amount).hp p).val = (s.hp p).val - amount := by
  simp [hurt, Nat.min_eq_left ((Nat.sub_le _ _).trans (s.hp_bounded p))]

theorem Vertex.heal_hp {r : Rules} (s : Vertex r) (p : Player) (amount : Nat) :
    ((s.heal p amount).hp p).val = min ((s.hp p).val + amount) r.hpMax := by
  simp [heal]

theorem Vertex.hurt_other {r : Rules} (s : Vertex r) (p : Player) (amount : Nat) :
    (s.hurt p amount).hp p.other = s.hp p.other := by simp [hurt]

theorem Vertex.heal_other {r : Rules} (s : Vertex r) (p : Player) (amount : Nat) :
    (s.heal p amount).hp p.other = s.hp p.other := by simp [heal]

/-- Combat admission and adventure validity use the same shared rulebook. -/
def Admissible (r : Rules) (c : CharacterStateCombat) : Prop := c.WellFormed r

instance (r : Rules) (c : CharacterStateCombat) : Decidable (Admissible r c) :=
  inferInstanceAs (Decidable (c.WellFormed r))

/-- A character can enter this generic combat model only with evidence that it
respects the shared rulebook. No per-character bounds are introduced. -/
structure Combatant (r : Rules) where
  character : CharacterStateCombat
  admissible : Admissible r character

def Combatant.create (r : Rules) (c : CharacterStateCombat) : Option (Combatant r) :=
  if h : Admissible r c then some ⟨c, h⟩ else none

theorem Combatant.create_isSome (r : Rules) (c : CharacterStateCombat) :
    (Combatant.create r c).isSome = true ↔ Admissible r c := by
  simp [create]

/-- All combat-specific input is the pair of bounded character snapshots.
The turn can be initialized from an initiative rule or chosen explicitly. -/
structure Setup (r : Rules) where
  characters : Player → Combatant r
  distinct : (characters .A).character.id ≠ (characters .B).character.id
  first : Player := .A

/-- An executable boundary: invalid characters or duplicate identities are
rejected before constructing a combat. Nothing is silently truncated. -/
def Setup.create (r : Rules) (a b : CharacterStateCombat) (first : Player := .A) :
    Option (Setup r) :=
  if ha : Admissible r a then
    if hb : Admissible r b then
      if hid : a.id ≠ b.id then
        some { characters := (fun p => match p with
          | .A => ⟨a, ha⟩
          | .B => ⟨b, hb⟩)
               distinct := hid
               first := first }
      else none
    else none
  else none

theorem Setup.create_isSome (r : Rules) (a b : CharacterStateCombat) (first : Player) :
    (Setup.create r a b first).isSome = true ↔
      Admissible r a ∧ Admissible r b ∧ a.id ≠ b.id := by
  by_cases ha : Admissible r a <;> by_cases hb : Admissible r b <;>
    by_cases hid : a.id = b.id <;> simp [create, ha, hb, hid]

def Setup.fromAdventure (r : Rules) (a b : CharacterState) (first : Player := .A) :
    Option (Setup r) := Setup.create r a.toCombat b.toCombat first

/-- A successful input check preserves every supplied mechanical field. -/
theorem Setup.create_preserves (r : Rules) (a b : CharacterStateCombat) (first : Player)
    (c : Setup r) (hc : Setup.create r a b first = some c) :
    (c.characters .A).character = a ∧ (c.characters .B).character = b ∧ c.first = first := by
  unfold create at hc
  split_ifs at hc with ha hb hid
  · cases Option.some.inj hc
    exact ⟨rfl, rfl, rfl⟩

def Setup.initial {r : Rules} (c : Setup r) : Vertex r where
  turn := c.first
  hp p := clamp r.hpMax (c.characters p).character.hp.toNat
  guarded := false
  stock p i := clamp r.stockMax
    ((((c.characters p).character.inventory[i.val]?).map (·.quantity)).getD 0)
  remaining p key := match key with
    | .initial owner i => if p = owner then
        clamp r.durationMax ((((c.characters p).character.effects[i.val]?).map
          (fun e => e.remaining.val)).getD 0) else 0
    | .item _ _ _ => 0

theorem Setup.initial_hp {r : Rules} (c : Setup r) (p : Player) :
    (c.initial.hp p).val = (c.characters p).character.hp.toNat := by
  have hc := (c.characters p).admissible
  simp only [Admissible, CharacterStateCombat.WellFormed] at hc
  have hb : (c.characters p).character.hp.toNat ≤ r.hpMax := by omega
  simp [initial, Nat.min_eq_left hb]

/-- Adventure HP is read as-is, with no reset to HPmax or ST. -/
theorem Setup.fromAdventure_initial_hp (r : Rules) (a b : CharacterState) (first : Player)
    (c : Setup r) (hc : Setup.fromAdventure r a b first = some c) :
    (c.initial.hp .A).val = a.hp.toNat ∧ (c.initial.hp .B).val = b.hp.toNat := by
  have h := Setup.create_preserves r a.toCombat b.toCombat first c hc
  rw [c.initial_hp .A, c.initial_hp .B, h.1, h.2.1]
  exact ⟨rfl, rfl⟩

/-- A live entry vertex corresponds exactly to strictly positive HP in both
supplied character snapshots. No reset to maximum HP takes place. -/
theorem Setup.initial_alive_iff {r : Rules} (c : Setup r) :
    c.initial.output = none ↔ ∀ p, 0 < (c.characters p).character.hp := by
  rw [Vertex.output_none_iff, c.initial_hp .A, c.initial_hp .B]
  constructor
  · rintro ⟨ha, hb⟩ p
    cases p <;> omega
  · intro h
    have ha := h .A
    have hb := h .B
    constructor <;> omega

def Setup.item? {r : Rules} (c : Setup r) (p : Player) (i : Fin r.itemSlots) :
    Option ItemMechanics := ((c.characters p).character.inventory[i.val]?).map (·.item)

def Setup.effect? {r : Rules} (c : Setup r) (p : Player) (i : Fin r.itemSlots)
    (e : Fin r.effectsPerSource) : Option ItemEffect :=
  (c.item? p i).bind (fun item => item.effects[e.val]?)

def Setup.modifier? {r : Rules} (c : Setup r) : EffectKey r → Option Modifier
  | .initial p i => ((c.characters p).character.effects[i.val]?).map (·.modifier)
  | .item p i e => match c.effect? p i e with
    | some (.timedOnUse _ modifier _) => some modifier
    | _ => none

def Setup.equipped {r : Rules} (c : Setup r) (p : Player) (i : Fin r.itemSlots) : Bool :=
  match c.item? p i with
  | none => false
  | some item =>
    let eq := (c.characters p).character.equipment
    eq.weapon == some item.id || eq.armor == some item.id

/-- Attack and defend are shared by both players. Bonus identifies an inventory
slot and is enabled only when that item is available and has a use effect. -/
inductive Action (r : Rules) where
  | attack
  | defend
  | bonus (item : Fin r.itemSlots)
  deriving DecidableEq, Fintype

def ItemEffect.usable : ItemEffect → Bool
  | .onUse _ _ | .timedOnUse _ _ _ => true
  | _ => false

def Setup.enabled {r : Rules} (c : Setup r) (s : Vertex r) : Action r → Bool
  | .attack | .defend => true
  | .bonus i => (s.stock s.turn i).val > 0 &&
      ((c.item? s.turn i).map (fun item => item.effects.any ItemEffect.usable)).getD false

/-- These counts concern the universal ambient graph. Actual reachable vertices
can be far fewer. They are independent of character identities and statistics. -/
theorem card_hp_layers (r : Rules) :
    Fintype.card (Player × (Player → Fin (r.hpMax + 1))) = 2 * (r.hpMax + 1)^2 := by
  simp [Fintype.card_pi, Fintype.card_fin, show Fintype.card Player = 2 by decide]

theorem card_vertex (r : Rules) :
    Fintype.card (Vertex r) =
      4 * (r.hpMax + 1)^2 * (r.stockMax + 1)^(2 * r.itemSlots) *
        (r.durationMax + 1)^(2 * Fintype.card (EffectKey r)) := by
  rw [Fintype.card_congr (Vertex.equiv r)]
  simp [Fintype.card_pi, show Fintype.card Player = 2 by decide, ← pow_mul]
  ring

end MarkovRPG.Combat
