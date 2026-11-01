import Rpg.Probability.Distribution
import Init.GrindInstances.Ring.Rat
import Init.Grind.Ordered.Rat

/-! Binomial expectations, exact integer evaluation, and tail probabilities. -/
namespace Rpg.Probability.Confidence

/-- Expectation of f(K) when K is the count of successes in n independent Bernoulli(p) trials. -/
def binomialExpectation (p : Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f => (1-p) * binomialExpectation p n f +
      p * binomialExpectation p n (fun k => f (k+1))

/-- Constants retain their expectation under the sampling law. -/
theorem constant (p c : Rat) (n : Nat) : binomialExpectation p n (fun _ => c) = c := by
  induction n with
  -- With no trials, the constant is evaluated directly.
  | zero => rfl
  -- The two Bernoulli weights sum to one.
  | succ n ih =>
    simp only [binomialExpectation, ih]
    grind

/-- Expectation is additive. -/
theorem add (p : Rat) (n : Nat) (f g : Nat → Rat) :
    binomialExpectation p n (fun k => f k + g k) =
      binomialExpectation p n f + binomialExpectation p n g := by
  induction n generalizing f g with
  -- With no trials, addition is evaluated directly.
  | zero => rfl
  -- Apply additivity after either outcome of the next trial.
  | succ n ih =>
    simp only [binomialExpectation, ih]
    grind

/-- A rational scalar can be pulled outside the expectation. -/
theorem scale (p c : Rat) (n : Nat) (f : Nat → Rat) :
    binomialExpectation p n (fun k => c * f k) = c * binomialExpectation p n f := by
  induction n generalizing f with
  -- With no trials, scaling is evaluated directly.
  | zero => rfl
  -- Pull out the scalar after either outcome of the next trial.
  | succ n ih =>
    simp only [binomialExpectation, ih]
    grind

/-- Nonnegative Bernoulli weights preserve pointwise inequalities. -/
theorem monotone (p : Rat)
    -- The success probability is nonnegative.
    (hp : 0 ≤ p)
    -- The failure probability is nonnegative.
    (hp1 : p ≤ 1) (n : Nat) (f g : Nat → Rat)
    -- The count functions are ordered everywhere.
    (h : ∀ k, f k ≤ g k) :
    binomialExpectation p n f ≤ binomialExpectation p n g := by
  induction n generalizing f g with
  -- Only the zero count is possible.
  | zero => exact h 0
  -- Both weighted comparisons preserve the order.
  | succ n ih =>
    have left := ih f g h
    have right := ih (fun k => f (k+1)) (fun k => g (k+1)) (fun k => h (k+1))
    simp only [binomialExpectation]
    have nonnegative : 0 ≤ 1-p := by grind
    have hleft := Rat.mul_le_mul_of_nonneg_left left nonnegative
    have hright := Rat.mul_le_mul_of_nonneg_left right hp
    grind

/-- Comparisons need only hold on possible success counts. -/
theorem support_monotone (p : Rat)
    -- The success probability is nonnegative.
    (hp : 0 ≤ p)
    -- The failure probability is nonnegative.
    (hp1 : p ≤ 1) (n : Nat) (f g : Nat → Rat)
    -- The count functions are ordered on possible counts.
    (h : ∀ k, k ≤ n → f k ≤ g k) :
    binomialExpectation p n f ≤ binomialExpectation p n g := by
  induction n generalizing f g with
  -- Only the zero count is possible.
  | zero => exact h 0 (by omega)
  -- The next trial leaves the count unchanged or adds one.
  | succ n ih =>
    have left := ih f g (fun k hk => h k (by omega))
    have right := ih (fun k => f (k+1)) (fun k => g (k+1))
      (fun k hk => h (k+1) (by omega))
    simp only [binomialExpectation]
    have nonnegative : 0 ≤ 1-p := by grind
    have hl := Rat.mul_le_mul_of_nonneg_left left nonnegative
    have hr := Rat.mul_le_mul_of_nonneg_left right hp
    grind

/-- Increasing Bernoulli probability increases expectations of increasing count functions. -/
theorem probability_monotone (p q : Rat)
    -- The smaller probability is nonnegative.
    (hp : 0 ≤ p)
    -- The probabilities are ordered.
    (hpq : p ≤ q)
    -- The larger probability is at most one.
    (hq1 : q ≤ 1) (n : Nat) (f : Nat → Rat)
    -- More successes cannot reduce the statistic.
    (increasing : ∀ k, f k ≤ f (k+1)) :
    binomialExpectation p n f ≤ binomialExpectation q n f := by
  induction n generalizing f with
  -- No trials makes the probability irrelevant.
  | zero => exact Rat.le_refl
  -- Increasing each trial's success probability preserves the order.
  | succ n ih =>
    have left := ih f increasing
    have right := ih (fun k => f (k+1)) (fun k => increasing (k+1))
    have ordered := monotone q (by grind) hq1 n f (fun k => f (k+1)) increasing
    have hl := Rat.mul_le_mul_of_nonneg_left left (show 0 ≤ 1-p by grind)
    have hr := Rat.mul_le_mul_of_nonneg_left right hp
    have spread := Rat.mul_nonneg (show 0 ≤ q-p by grind)
      (show 0 ≤ binomialExpectation q n (fun k => f (k+1)) - binomialExpectation q n f by grind)
    simp only [binomialExpectation]
    grind

/-- One integer Bernstein step, treating entries beyond the vector as zero. -/
def blend (a b : Int) : List Int → List Int
  | [] => []
  | x :: rest => ((b-a)*x + a*rest.getD 0 0) :: blend a b rest

/-- Evaluate a count statistic with integer arithmetic, keeping the denominator outside. -/
def integerExpectation (a b : Int) : Nat → List Int → Int
  | 0, values => values.getD 0 0
  | n+1, values => integerExpectation a b n (blend a b values)

/-- Each blended entry is the weighted average of adjacent count values. -/
theorem blend_getD (a b : Int) (values : List Int) (k : Nat) :
    (blend a b values).getD k 0 = (b-a)*values.getD k 0+a*values.getD (k+1) 0 := by
  induction values generalizing k with
  -- Missing entries contribute zero.
  | nil => simp [blend]
  -- Separate the first entry from the remaining entries.
  | cons x rest ih =>
    cases k with
    -- The first entry is the defining blend.
    | zero => simp [blend, List.getD]
    -- Later entries follow by induction.
    | succ k => simpa [blend, List.getD] using ih k

/-- The integer evaluator equals the independent-Bernoulli expectation after scaling. -/
theorem integerExpectation_correct (p : Rat) (a b : Int)
    (ratio : (b : Rat)*p = (a : Rat)) (n : Nat) (values : List Int) :
    ((integerExpectation a b n values : Int) : Rat) =
      (b : Rat)^n * binomialExpectation p n (fun k => (values.getD k 0 : Rat)) := by
  induction n generalizing values with
  -- No scaling is needed for zero trials.
  | zero => simp [integerExpectation, binomialExpectation, List.getD]
  -- One integer blend supplies one Bernoulli step and one denominator factor.
  | succ n ih =>
    rw [integerExpectation, ih]
    have blended : (fun k => ((blend a b values).getD k 0 : Rat)) =
        (fun k => ((b : Rat)-(a : Rat))*(values.getD k 0 : Rat)+
          (a : Rat)*(values.getD (k+1) 0 : Rat)) := by
      funext k
      rw [blend_getD]
      simp
    rw [blended, add, scale, scale]
    simp only [binomialExpectation, Rat.pow_succ]
    grind

/-- Divide the integer numerator by the common Bernoulli denominator. -/
def exactExpectation (p : Rat) (n : Nat) (values : List Int) : Rat :=
  (integerExpectation p.num p.den n values : Rat) / (p.den : Rat)^n

/-- Executable evaluation agrees with the binomial model on any finite count table. -/
theorem exactExpectation_correct (p : Rat) (n : Nat) (values : List Int) :
    exactExpectation p n values = binomialExpectation p n (fun k => (values.getD k 0 : Rat)) := by
  have dpos : (0 : Rat) < (p.den : Rat) := Rat.natCast_pos.mpr (by have := p.den_nz; omega)
  have frac : (p.num : Rat) / (p.den : Rat) = p := by
    simpa only [Rat.divInt_eq_div, Rat.intCast_natCast] using Rat.num_divInt_den p
  have ratio : ((p.den : Int) : Rat) * p = (p.num : Rat) := by
    simp only [Rat.intCast_natCast]
    rw [← frac]
    grind
  unfold exactExpectation
  rw [integerExpectation_correct p p.num p.den ratio]
  simp only [Rat.intCast_natCast]
  have positive := Rat.pow_pos (n := n) dpos
  grind

/-- Exact binomial probability of at most k successes; the table has only k+1 entries. -/
def lowerTail (p : Rat) (n k : Nat) : Rat :=
  exactExpectation p n (List.replicate (k+1) 1)

/-- Exact binomial probability of at least k successes. -/
def upperTail (p : Rat) (n k : Nat) : Rat :=
  match k with
  | 0 => 1
  | k+1 => 1-lowerTail p n k

/-- The lower-tail computation uses the actual independent-Bernoulli law. -/
theorem lowerTail_eq (p : Rat) (n k : Nat) : lowerTail p n k =
    binomialExpectation p n (fun j => if j ≤ k then 1 else 0) := by
  unfold lowerTail
  rw [exactExpectation_correct]
  congr 1
  funext j
  simp only [List.getD, List.getElem?_replicate]
  split <;> simp only [Option.getD_some, Option.getD_none]
  all_goals split <;> first | omega | rfl

/-- The upper-tail computation uses the actual independent-Bernoulli law. -/
theorem upperTail_eq (p : Rat) (n k : Nat) : upperTail p n k =
    binomialExpectation p n (fun j => if k ≤ j then 1 else 0) := by
  cases k with
  -- Every count is at least zero.
  | zero => simp [upperTail, constant]
  -- The upper tail is the complement of the preceding lower tail.
  | succ k =>
    have complement : (fun j => if k+1 ≤ j then (1 : Rat) else 0) =
        (fun j => 1 + (-1)*(if j ≤ k then (1 : Rat) else 0)) := by
      funext j
      split <;> split <;> first | omega | decide +kernel
    rw [upperTail, complement, add, constant, scale, lowerTail_eq]
    grind

/-- Upper-tail probability increases with the Bernoulli probability. -/
theorem upperTail_monotone (p q : Rat)
    -- The smaller probability is nonnegative.
    (hp : 0 ≤ p)
    -- The probabilities are ordered.
    (hpq : p ≤ q)
    -- The larger probability is at most one.
    (hq1 : q ≤ 1)
    (n k : Nat) : upperTail p n k ≤ upperTail q n k := by
  rw [upperTail_eq, upperTail_eq]
  apply probability_monotone p q hp hpq hq1
  intro j
  split <;> split <;> first | omega | decide +kernel

/-- Lower-tail probability decreases with the Bernoulli probability. -/
theorem lowerTail_antitone (p q : Rat)
    -- The smaller probability is nonnegative.
    (hp : 0 ≤ p)
    -- The probabilities are ordered.
    (hpq : p ≤ q)
    -- The larger probability is at most one.
    (hq1 : q ≤ 1)
    (n k : Nat) : lowerTail q n k ≤ lowerTail p n k := by
  have upper := probability_monotone p q hp hpq hq1 n
    (fun j => if j ≤ k then (0 : Rat) else 1) (by
      intro j
      split <;> split <;> first | omega | decide +kernel)
  have complement : (fun j => if j ≤ k then (0 : Rat) else 1) =
      (fun j => 1 + (-1)*(if j ≤ k then (1 : Rat) else 0)) := by
    funext j
    split <;> decide +kernel
  rw [complement, add, add, constant, constant, scale, scale] at upper
  rw [lowerTail_eq, lowerTail_eq]
  grind

/-- A nonempty set of counts bounded by n has a largest count. -/
theorem bounded_max (P : Nat → Prop) (n : Nat) (witness : ∃ k, k ≤ n ∧ P k) :
    ∃ m, m ≤ n ∧ P m ∧ ∀ k, k ≤ n → P k → k ≤ m := by
  classical
  induction n with
  -- Zero is the only possible witness.
  | zero =>
    obtain ⟨k, hk, h⟩ := witness
    have eq : k = 0 := by omega
    subst k
    exact ⟨0, by omega, h, by intros; omega⟩
  -- Check whether the new endpoint belongs to the set.
  | succ n ih =>
    by_cases last : P (n+1)
    -- The endpoint is the largest possible member.
    · exact ⟨n+1, by omega, last, by intros; omega⟩
    -- Otherwise the previous maximum remains valid.
    · have earlier : ∃ k, k ≤ n ∧ P k := by
        obtain ⟨k, hk, h⟩ := witness
        have ne : k ≠ n+1 := by
          intro eq
          subst k
          exact last h
        exact ⟨k, by omega, h⟩
      obtain ⟨m, hm, h, max⟩ := ih earlier
      refine ⟨m, by omega, h, ?_⟩
      intro k hk hkP
      have ne : k ≠ n+1 := by
        intro eq
        subst k
        exact last hkP
      have kn : k ≤ n := by omega
      exact max k kn hkP

/-- A nonempty bounded set of counts has a smallest count. -/
theorem bounded_min (P : Nat → Prop) (n : Nat) (witness : ∃ k, k ≤ n ∧ P k) :
    ∃ m, m ≤ n ∧ P m ∧ ∀ k, k ≤ n → P k → m ≤ k := by
  classical
  induction n with
  -- Zero is the only possible witness.
  | zero =>
    obtain ⟨k, hk, h⟩ := witness
    have eq : k = 0 := by omega
    subst k
    exact ⟨0, by omega, h, by intros; omega⟩
  -- Check whether the smaller range contains a member.
  | succ n ih =>
    by_cases earlier : ∃ k, k ≤ n ∧ P k
    -- Its minimum remains the minimum of the larger range.
    · obtain ⟨m, hm, h, min⟩ := ih earlier
      refine ⟨m, by omega, h, ?_⟩
      intro k hk hkP
      by_cases kn : k ≤ n
      -- An earlier member is bounded by the previous minimum.
      · exact min k kn hkP
      -- The new endpoint is larger than that minimum.
      · omega
    -- The new endpoint is the only possible member.
    · obtain ⟨m, hm, h⟩ := witness
      refine ⟨m, hm, h, ?_⟩
      intro k hk hkP
      have kn : ¬ k ≤ n := fun kn => earlier ⟨k, kn, hkP⟩
      omega

/-- A lower-tail p-value falls below alpha with probability at most alpha. -/
theorem lowerTail_error (p alpha : Rat) (n : Nat)
    -- The success probability is nonnegative.
    (hp : 0 ≤ p)
    -- The success probability is at most one.
    (hp1 : p ≤ 1)
    -- The permitted tail error is nonnegative.
    (ha : 0 ≤ alpha) :
    binomialExpectation p n (fun k => if lowerTail p n k < alpha then 1 else 0) ≤ alpha := by
  by_cases witness : ∃ k, k ≤ n ∧ lowerTail p n k < alpha
  -- All rejected counts lie below the largest rejected count.
  · obtain ⟨m, _, small, largest⟩ := bounded_max _ n witness
    have bound := support_monotone p hp hp1 n
      (fun k => if lowerTail p n k < alpha then 1 else 0)
      (fun k => if k ≤ m then 1 else 0) (by
        intro k hk
        split
        -- A rejected count belongs to the bounding tail.
        · next h => simp [largest k hk h]
        -- A count that is not rejected contributes zero.
        · split <;> decide +kernel)
    rw [← lowerTail_eq] at bound
    exact Rat.le_trans bound (Rat.le_of_lt small)
  -- No possible count is rejected.
  · have bound := support_monotone p hp hp1 n
      (fun k => if lowerTail p n k < alpha then 1 else 0) (fun _ => 0) (by
        intro k hk
        have h : ¬ lowerTail p n k < alpha := fun h => witness ⟨k, hk, h⟩
        simp only [h, ite_false]
        exact Rat.le_refl)
    rw [constant] at bound
    exact Rat.le_trans bound ha

/-- An upper-tail p-value falls below alpha with probability at most alpha. -/
theorem upperTail_error (p alpha : Rat) (n : Nat)
    -- The success probability is nonnegative.
    (hp : 0 ≤ p)
    -- The success probability is at most one.
    (hp1 : p ≤ 1)
    -- The permitted tail error is nonnegative.
    (ha : 0 ≤ alpha) :
    binomialExpectation p n (fun k => if upperTail p n k < alpha then 1 else 0) ≤ alpha := by
  by_cases witness : ∃ k, k ≤ n ∧ upperTail p n k < alpha
  -- All rejected counts lie above the smallest rejected count.
  · obtain ⟨m, _, small, smallest⟩ := bounded_min _ n witness
    have bound := support_monotone p hp hp1 n
      (fun k => if upperTail p n k < alpha then 1 else 0)
      (fun k => if m ≤ k then 1 else 0) (by
        intro k hk
        split
        -- A rejected count belongs to the bounding tail.
        · next h => simp [smallest k hk h]
        -- A count that is not rejected contributes zero.
        · split <;> decide +kernel)
    rw [← upperTail_eq] at bound
    exact Rat.le_trans bound (Rat.le_of_lt small)
  -- No possible count is rejected.
  · have bound := support_monotone p hp hp1 n
      (fun k => if upperTail p n k < alpha then 1 else 0) (fun _ => 0) (by
        intro k hk
        have h : ¬ upperTail p n k < alpha := fun h => witness ⟨k, hk, h⟩
        simp only [h, ite_false]
        exact Rat.le_refl)
    rw [constant] at bound
    exact Rat.le_trans bound ha

end Rpg.Probability.Confidence
