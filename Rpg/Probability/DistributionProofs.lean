import Rpg.Probability.Distribution
import Init.GrindInstances.Ring.Rat
import Init.Grind.Ordered.Rat

/-! Probability laws for the executable finite distributions. Equality of expectations,
rather than equality of list representations, is the semantic equivalence. -/
namespace Rpg.Probability

attribute [local simp] Rat.zero_add Rat.add_zero Rat.zero_mul Rat.mul_zero Rat.one_mul Rat.mul_one

def weightedSum (xs : List (α × Rat)) (f : α → Rat) : Rat :=
  (xs.map fun (x, p) => p * f x).sum

def Distribution.expect (d : Distribution α) (f : α → Rat) : Rat := weightedSum d.entries f

@[simp] theorem weightedSum_nil (f : α → Rat) : weightedSum [] f = 0 := rfl
@[simp] theorem weightedSum_cons (x : α) (p : Rat) (xs : List (α × Rat)) (f : α → Rat) :
    weightedSum ((x, p) :: xs) f = p * f x + weightedSum xs f := rfl

theorem weightedSum_append (xs ys : List (α × Rat)) (f : α → Rat) :
    weightedSum (xs ++ ys) f = weightedSum xs f + weightedSum ys f := by
  induction xs with
  | nil => simp
  | cons x xs ih => rcases x with ⟨x,p⟩; simp [ih]; grind

theorem weightedSum_scale (xs : List (α × Rat)) (c : Rat) (f : α → Rat) :
    weightedSum (xs.map fun (x,p) => (x,c*p)) f = c * weightedSum xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih => rcases x with ⟨x,p⟩; simp [ih]; grind

theorem weightedSum_add (xs : List (α × Rat)) (f g : α → Rat) :
    weightedSum xs (fun x => f x + g x) = weightedSum xs f + weightedSum xs g := by
  induction xs with
  | nil => simp
  | cons x xs ih => rcases x with ⟨x,p⟩; simp [ih]; grind

theorem weightedSum_mul (xs : List (α × Rat)) (c : Rat) (f : α → Rat) :
    weightedSum xs (fun x => c * f x) = c * weightedSum xs f := by
  induction xs with
  | nil => simp
  | cons x xs ih => rcases x with ⟨x,p⟩; simp [ih]; grind

theorem addWeight_sum [DecidableEq α] (x : α) (p : Rat) (xs : List (α × Rat)) (f : α → Rat) :
    weightedSum (addWeight x p xs) f = p * f x + weightedSum xs f := by
  induction xs with
  | nil => simp only [addWeight]; split <;> simp_all
  | cons e xs ih =>
    rcases e with ⟨y,q⟩
    simp only [addWeight]
    split
    · next h => subst y; simp_all; grind
    · simp [ih]; grind

@[simp] theorem Distribution.expect_collect [DecidableEq α] (d : Distribution α) (f : α → Rat) :
    d.collect.expect f = d.expect f := by
  rcases d with ⟨xs⟩
  simp only [Distribution.collect, Distribution.expect]
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨x,p⟩; simp [List.foldr, addWeight_sum, ih]

@[simp] theorem Distribution.expect_pure (x : α) (f : α → Rat) :
    (pure x : Distribution α).expect f = f x := by
  simp [Distribution.expect, weightedSum, pure, Pure.pure]

theorem Distribution.expect_bind (d : Distribution α) (k : α → Distribution β) (f : β → Rat) :
    (d.bind k).expect f = d.expect (fun x => (k x).expect f) := by
  rcases d with ⟨xs⟩
  simp only [Distribution.bind, Distribution.expect]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨x,p⟩
    simp [List.flatMap_cons, weightedSum_append, weightedSum_scale, ih]

@[simp] theorem Distribution.expect_map (d : Distribution α) (g : α → β) (f : β → Rat) :
    (g <$> d).expect f = d.expect (fun x => f (g x)) := by
  change (d.bind fun x => pure (g x)).expect f = _
  simp [Distribution.expect_bind]

theorem Distribution.mass_eq_expect (d : Distribution α) (test : α → Bool) :
    d.mass test = d.expect (fun x => if test x then 1 else 0) := by
  simp only [Distribution.mass, Distribution.expect, weightedSum]
  congr 1
  apply List.map_congr_left
  intro e _
  split <;> simp_all

@[simp] theorem Distribution.mass_collect [DecidableEq α] (d : Distribution α) (test : α → Bool) :
    d.collect.mass test = d.mass test := by simp [Distribution.mass_eq_expect]

theorem weightedSum_mono (xs : List (α × Rat)) (positive : ∀ e ∈ xs, 0 ≤ e.2)
    (f g : α → Rat) (h : ∀ e ∈ xs, f e.1 ≤ g e.1) : weightedSum xs f ≤ weightedSum xs g := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons e xs ih =>
    rcases e with ⟨x,p⟩
    have tail := ih (fun e he => positive e (by simp [he])) (fun e he => h e (by simp [he]))
    have head := Rat.mul_le_mul_of_nonneg_left (h (x,p) (by simp)) (positive (x,p) (by simp))
    simp only [weightedSum_cons]
    grind

theorem Distribution.expect_mono (d : Distribution α) (valid : d.Valid)
    (f g : α → Rat) (h : ∀ e ∈ d.entries, f e.1 ≤ g e.1) : d.expect f ≤ d.expect g :=
  weightedSum_mono d.entries valid.1 f g h

theorem weightedSum_one (xs : List (α × Rat)) : weightedSum xs (fun _ => 1) = (xs.map Prod.snd).sum := by
  simp [weightedSum]

@[simp] theorem Distribution.expect_const (d : Distribution α) (valid : d.Valid) (c : Rat) :
    d.expect (fun _ => c) = c := by
  have h := weightedSum_mul d.entries c (fun _ => 1)
  simp only [Rat.mul_one, weightedSum_one, valid.2] at h
  simpa [Distribution.expect] using h

@[simp] theorem Distribution.valid_pure (x : α) : (pure x : Distribution α).Valid := by
  simp [Distribution.Valid, pure, Pure.pure]
  decide

theorem Distribution.valid_bind (d : Distribution α) (k : α → Distribution β)
    (hd : d.Valid) (hk : ∀ x, (k x).Valid) : (d.bind k).Valid := by
  constructor
  · intro e he
    simp only [Distribution.bind, List.mem_flatMap, List.mem_map] at he
    obtain ⟨⟨x,p⟩, hx, ⟨y,q⟩, hy, rfl⟩ := he
    exact Rat.mul_nonneg (hd.1 _ hx) ((hk x).1 _ hy)
  · rw [← weightedSum_one]
    change (d.bind k).expect (fun _ => 1) = 1
    simp [Distribution.expect_bind, Distribution.expect_const _ hd, fun x => Distribution.expect_const (k x) (hk x)]

theorem Distribution.valid_map (d : Distribution α) (g : α → β) (hd : d.Valid) : (g <$> d).Valid :=
  d.valid_bind (fun x => pure (g x)) hd (fun _ => Distribution.valid_pure _)

theorem addWeight_nonnegative [DecidableEq α] (x : α) (p : Rat) (xs : List (α × Rat))
    (hp : 0 ≤ p) (hs : ∀ e ∈ xs, 0 ≤ e.2) : ∀ e ∈ addWeight x p xs, 0 ≤ e.2 := by
  induction xs with
  | nil => simp only [addWeight]; split <;> simp_all
  | cons e xs ih =>
    rcases e with ⟨y,q⟩
    have hq := hs (y,q) (by simp)
    have ht : ∀ e ∈ xs, 0 ≤ e.2 := fun e he => hs e (by simp [he])
    simp only [addWeight]
    split
    · intro e he; simp only [List.mem_cons] at he; rcases he with rfl | he
      · change 0 ≤ p + q; grind
      · exact ht e he
    · intro e he; simp only [List.mem_cons] at he; rcases he with rfl | he
      · exact hq
      · exact ih ht e he

theorem Distribution.valid_collect [DecidableEq α] (d : Distribution α) (hd : d.Valid) : d.collect.Valid := by
  constructor
  · rcases d with ⟨xs⟩
    have hs := hd.1
    clear hd
    change ∀ e ∈ xs.foldr (fun (x,p) acc => addWeight x p acc) [], 0 ≤ e.2
    induction xs with
    | nil => simp
    | cons e xs ih =>
      rcases e with ⟨x,p⟩
      exact addWeight_nonnegative x p _ (hs (x,p) (by simp)) (ih (fun e he => hs e (by simp [he])))
  · rw [← weightedSum_one]
    change d.collect.expect (fun _ => 1) = 1
    simp [Distribution.expect_const _ hd]

theorem uniform_total (xs : List α) (c : Rat) :
    weightedSum (xs.map fun x => (x,c)) (fun _ => 1) = (xs.length : Rat) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; grind

theorem uniform_valid (xs : List α) (hne : xs ≠ []) : (uniform xs).Valid := by
  have hlen : 0 < xs.length := List.length_pos_iff.mpr hne
  have hp : (0 : Rat) < xs.length := Rat.natCast_pos.mpr hlen
  constructor
  · intro e he
    simp only [uniform, List.mem_map] at he
    obtain ⟨x, _, rfl⟩ := he
    change 0 ≤ 1 / (xs.length : Rat)
    simpa [Rat.div_def] using Rat.le_of_lt (Rat.inv_pos.mpr hp)
  · rw [← weightedSum_one]
    change weightedSum (xs.map fun x => (x, 1 / (xs.length : Rat))) (fun _ => 1) = 1
    rw [uniform_total]
    grind

theorem dice_valid (n : Nat) : (dice n).Valid := by
  induction n with
  | zero => exact Distribution.valid_pure _
  | succ n ih =>
    apply Distribution.valid_collect
    apply Distribution.valid_bind
    · exact uniform_valid _ (by decide)
    · intro a
      apply Distribution.valid_bind _ _ ih
      intro b
      exact Distribution.valid_pure _

/-- The probability of an event lies in the unit interval. -/
theorem Distribution.mass_bounds (d : Distribution α) (hd : d.Valid) (test : α → Bool) :
    0 ≤ d.mass test ∧ d.mass test ≤ 1 := by
  rw [Distribution.mass_eq_expect]
  constructor
  · have h := d.expect_mono hd (fun _ => 0) (fun x => if test x then 1 else 0) (by
      intro e _; split <;> decide)
    simpa [Distribution.expect_const _ hd] using h
  · have h := d.expect_mono hd (fun x => if test x then 1 else 0) (fun _ => 1) (by
      intro e _; split <;> decide)
    simpa [Distribution.expect_const _ hd] using h

/-- Equality of weights is checked by exact cancellation, independent of entry order. -/
def Distribution.sameWeights [DecidableEq α] (d e : Distribution α) : Prop :=
  ∀ v ∈ (Distribution.mk (d.entries ++ e.entries.map fun (x,p) => (x, -p))).collect.entries, v.2 = 0

instance [DecidableEq α] (d e : Distribution α) : Decidable (d.sameWeights e) := by
  unfold Distribution.sameWeights
  infer_instance

/-- The finite cancellation check proves equality for every observable. -/
theorem Distribution.sameWeights_sound [DecidableEq α] (d e : Distribution α)
    (h : d.sameWeights e) (f : α → Rat) : d.expect f = e.expect f := by
  let difference := Distribution.mk (d.entries ++ e.entries.map fun (x,p) => (x,-p))
  have hc := difference.expect_collect f
  have hz : difference.collect.expect f = 0 := by
    change weightedSum difference.collect.entries f = 0
    have zero : ∀ (xs : List (α × Rat)), (∀ v ∈ xs, v.2 = 0) → weightedSum xs f = 0 := by
      intro xs
      induction xs with
      | nil => intro _; rfl
      | cons v xs ih =>
        intro hz
        obtain ⟨x,p⟩ := v
        have hp : p = 0 := hz (x,p) (by simp)
        have ht := ih (fun v hv => hz v (by simp [hv]))
        simp only [weightedSum_cons, hp, ht, Rat.zero_mul, Rat.add_zero]
    exact zero _ h
  rw [hz] at hc
  change 0 = weightedSum (d.entries ++ e.entries.map fun (x,p) => (x,-p)) f at hc
  have neg : (e.entries.map fun (x,p) => (x,-p)) =
      (e.entries.map fun (x,p) => (x,(-1 : Rat)*p)) := by
    apply List.map_congr_left
    intro x _
    congr 1
    grind
  rw [weightedSum_append, neg, weightedSum_scale] at hc
  change 0 = d.expect f + (-1) * e.expect f at hc
  grind

end Rpg.Probability
