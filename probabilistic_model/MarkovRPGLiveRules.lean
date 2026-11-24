import add_rules

/-! Executable workshop adapters. They reuse the generic character patches,
additional properties and timestamp-aware duration predicate from `add_rules`.
The current UI profile has two fighters, static equipment, ST/HT 10 and HP 0..3.
No theorem below claims support for timed effects or consumable item actions. -/
namespace MarkovRPG.Workshop
open scoped BigOperators NNReal
set_option backward.isDefEq.respectTransparency false

def equippedBeing (level : Nat) (weapon : MainRules.Weapon) : MainRules.Being :=
  { prototypeBeing level with weapon := weapon }

/-- Both new character statistics and the equipped weapons enter every row. -/
def equippedDuelRows (heroLevel enemyLevel : Nat) (heroWeapon enemyWeapon : MainRules.Weapon)
    (s : Fin 64) : List (Fin 64 × ℚ) :=
  if duelTerminal s then [(s, 1)] else
  let a := (duelHP s).1
  let b := (duelHP s).2
  let turn := duelTurn s
  let actor := equippedBeing (if turn = 0 then heroLevel else enemyLevel)
    (if turn = 0 then heroWeapon else enemyWeapon)
  let defender := equippedBeing (if turn = 0 then enemyLevel else heroLevel)
    (if turn = 0 then enemyWeapon else heroWeapon)
  let defenderHP := if turn = 0 then b else a
  let dodge := (if 3 * defenderHP < 6 then (defender.dodge + 1) / 2 else defender.dodge) +
    if duelGuard s then 2 else 0
  let dodgeP := rollProbability (fun roll => (MainRules.successRoll dodge roll).succeeded)
  let ordinary := rollProbability (fun roll => MainRules.successRoll actor.attackLevel roll == .success)
  let otherCritical := rollProbability (fun roll =>
    roll != 3 && MainRules.successRoll actor.attackLevel roll == .criticalSuccess)
  let maximized : ℚ := 1/216
  let hit := otherCritical + ordinary * (1 - dodgeP)
  let next := fun amount => if turn = 0 then duelIndex a (b - amount) 1 false
    else duelIndex (a - amount) b 0 false
  let injury := fun total => MainRules.injury actor.weapon.damageType 0
    (MainRules.basicDamage (actor.weapon.damage 10) actor.weapon.damageType total)
  [(next 0, (1 - maximized - hit) / 2)] ++
    ((List.range 6).map fun face => (next (injury (face + 1)), hit / 12)) ++
    [(next (injury 6), maximized / 2), (duelIndex a b (1 - turn) true, 1/2)]

theorem equippedDuelRows_original (enemyLevel : Nat) :
    equippedDuelRows 12 enemyLevel .punch .punch = duelRows enemyLevel := by
  funext s
  simp only [equippedDuelRows, duelRows, equippedBeing, prototypeBeing]
  simp only [ite_self]
  split <;> rfl

/-- The UI's finite character profile, using the existing complete Character. -/
def liveCharacter (hp dx iq : Nat) (weapon : MainRules.Weapon) : CharacterState :=
  { character := Character.ofBeing ⟨0⟩ { equippedBeing dx weapon with name := "Player", iq := iq }
    hp := hp }

def liveRules : Combat.Rules := { prototypeRules with itemSlots := 2, stockMax := 1, effectsPerSource := 1 }

/-- Exact rational action rows retain individual actions before uniform mixing. -/
structure RationalActions (n m : Nat) where
  source : Fin m → Fin n
  mass : Fin m → Fin n → ℚ
  nonneg : ∀ a v, 0 ≤ mass a v
  normalized : ∀ a, ∑ v, mass a v = 1

/-- A positive uniform average exists exactly when an available action has
positive mass. This reuses the already checked averaging equation instead of
searching all actions again for every pair of vertices. Empty action sets are
handled explicitly; no extra nonemptiness assumption is introduced. -/
theorem RationalActions.edge_iff_positive_average (a : RationalActions n m)
    (s v : Fin n) :
    (∃ i, a.source i = s ∧ 0 < a.mass i v) ↔
      0 < ((Finset.univ.filter fun i => a.source i = s).sum fun i => a.mass i v) /
        ((Finset.univ.filter fun i => a.source i = s).card : ℚ) := by
  let available := Finset.univ.filter fun i => a.source i = s
  have hsum : (0 < available.sum (fun i => a.mass i v)) ↔
      ∃ i ∈ available, 0 < a.mass i v :=
    Finset.sum_pos_iff_of_nonneg (fun i _ => a.nonneg i v)
  change (∃ i, a.source i = s ∧ 0 < a.mass i v) ↔
    0 < available.sum (fun i => a.mass i v) / (available.card : ℚ)
  by_cases hempty : available = ∅
  · have hnone : ¬ ∃ i, a.source i = s ∧ 0 < a.mass i v := by
      rintro ⟨i, hi, _⟩
      have hm : i ∈ available := by simp [available, hi]
      simpa [hempty] using hm
    simp [hempty, hnone]
  · have hcard : (0 : ℚ) < available.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    rw [div_pos_iff_of_pos_right hcard, hsum]
    simp [available]

theorem weight_nonneg_of_entries (row : List (Fin n × ℚ))
    (h : ∀ e ∈ row, 0 ≤ e.2) (v : Fin n) : 0 ≤ weight row v := by
  apply List.sum_nonneg
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  split_ifs
  · exact h e he
  · exact le_rfl

/-- Duplicate destinations and zero-weight entries are supported. Negative
weights are excluded by the graph's existing nonnegativity proof. -/
theorem weight_pos_iff_entry (row : List (Fin n × ℚ)) (v : Fin n) :
    (∀ e ∈ row, 0 ≤ e.2) →
    (0 < weight row v ↔ ∃ e ∈ row, e.1 = v ∧ 0 < e.2) := by
  induction row with
  | nil => intro _; simp [weight]
  | cons e rest ih =>
    intro h
    have he : 0 ≤ e.2 := h e List.mem_cons_self
    have hr : ∀ x ∈ rest, 0 ≤ x.2 := fun x hx => h x (List.mem_cons_of_mem e hx)
    have hrest := weight_nonneg_of_entries rest hr v
    have htail := ih hr
    change 0 < (if e.1 = v then e.2 else 0) + weight rest v ↔ _
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [← htail]
    by_cases hv : e.1 = v
    · simp only [hv, ite_true, true_and]
      constructor
      · intro hp
        by_cases hh : 0 < e.2
        · exact Or.inl hh
        · exact Or.inr (by linarith)
      · intro hp
        rcases hp with hp | hp <;> linarith
    · simp [hv]

/-- Sparse destinations with strictly positive weight. The definition has no
search over vertices or actions. -/
def positiveTargets (row : List (Fin n × ℚ)) : List (Fin n) :=
  (row.filter fun e => decide (0 < e.2)).map Prod.fst

theorem weight_pos_iff_positiveTargets (row : List (Fin n × ℚ))
    (h : ∀ e ∈ row, 0 ≤ e.2) (v : Fin n) :
    0 < weight row v ↔ v ∈ positiveTargets row := by
  rw [weight_pos_iff_entry row v h]
  simp only [positiveTargets, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, hv, hp⟩
    exact ⟨e, ⟨he, hp⟩, hv⟩
  · rintro ⟨e, ⟨he, hp⟩, hv⟩
    exact ⟨e, he, hv, hp⟩

noncomputable section

def RationalActions.law (a : RationalActions n m) (i : Fin m) : PMF (Fin n) :=
  PMF.ofFintype (fun v => ENNReal.ofReal (a.mass i v)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => by exact_mod_cast a.nonneg i v)]
    simp only [← Rat.cast_sum, a.normalized, Rat.cast_one, ENNReal.ofReal_one])

@[simp] theorem RationalActions.support (a : RationalActions n m) (i : Fin m) (v : Fin n) :
    v ∈ (a.law i).support ↔ 0 < a.mass i v := by
  simp [RationalActions.law, PMF.mem_support_ofFintype_iff, ENNReal.ofReal_eq_zero,
    not_le, Rat.cast_pos]

/-- A computable form of the EXISTING additional properties, with a bridge
proving that the tests inspect the same action PMFs. Terminal loops alone are ignored. -/
def RationalActions.numericProperties (a : RationalActions n m) (terminal : Fin n → Bool)
    (x : ℚ) : Prop :=
  AdventureProperties.NoSmallCycles
    (fun s v => (s ≠ v ∨ terminal s = false) ∧ ∃ i, a.source i = s ∧ 0 < a.mass i v) ∧
  0 ≤ x ∧ x ≤ 1 ∧
    ((Finset.univ.filter fun i => terminal (a.source i) = false ∧
      (Finset.univ.filter fun v => 0 < a.mass i v).card = 1).card : ℚ) ≤
      x * (Finset.univ.filter fun i => terminal (a.source i) = false).card

/-- This is not a separate definition of valid graphs. -/
theorem RationalActions.additional_iff (a : RationalActions n m) (terminal : Fin n → Bool)
    (x : ℚ) :
    AdventureProperties.HasAdditionalProperties a.source {s | terminal s = true} a.law x ↔
      a.numericProperties terminal x := by
  have edges : AdventureProperties.eventEdges {s | terminal s = true}
      (AdventureProperties.decisionEdges Finset.univ a.source a.law) =
      (fun s v => (s ≠ v ∨ terminal s = false) ∧ ∃ i, a.source i = s ∧ 0 < a.mass i v) := by
    funext s v
    simp only [AdventureProperties.eventEdges, AdventureProperties.decisionEdges,
      Finset.mem_univ, true_and, Set.mem_setOf_eq, Bool.not_eq_true, RationalActions.support]
  simp only [AdventureProperties.HasAdditionalProperties, RationalActions.numericProperties, edges,
    AdventureProperties.HasDeterministicDecisionBound,
    AdventureProperties.deterministicDecisions, AdventureProperties.liveDecisions,
    AdventureProperties.IsDeterministic, AdventureProperties.outputs, RationalActions.support,
    Finset.filter_filter, Set.mem_setOf_eq, Bool.not_eq_true]

end
end MarkovRPG.Workshop
