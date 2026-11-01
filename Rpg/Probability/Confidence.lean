import Rpg.Probability.Fairness
import Init.GrindInstances.Ring.Rat
import Init.Grind.Ordered.Rat

/-!
Exact finite-sample probability calculations over rational Bernoulli laws.
Theorems here concern a specified independent-sampling model, not the law of
SplitMix64 and not the truth of `isFair` for one observed seed.
-/
namespace Rpg.Probability.Confidence

/-- Expectation of f(K) when K is the count of successes in n independent Bernoulli(p) trials. -/
def binomialExpectation (p : Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f => (1-p) * binomialExpectation p n f +
      p * binomialExpectation p n (fun k => f (k+1))

/-- Constants retain their expectation under the sampling law. -/
theorem constant (p c : Rat) (n : Nat) : binomialExpectation p n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [binomialExpectation, ih]; grind

/-- Expectation is additive. -/
theorem add (p : Rat) (n : Nat) (f g : Nat → Rat) :
    binomialExpectation p n (fun k => f k + g k) =
      binomialExpectation p n f + binomialExpectation p n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [binomialExpectation, ih]
    grind

/-- A rational scalar can be pulled outside the expectation. -/
theorem scale (p c : Rat) (n : Nat) (f : Nat → Rat) :
    binomialExpectation p n (fun k => c * f k) = c * binomialExpectation p n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [binomialExpectation, ih]; grind

/-- Nonnegative Bernoulli weights preserve pointwise inequalities. -/
theorem monotone (p : Rat) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat)
    (f g : Nat → Rat) (h : ∀ k, f k ≤ g k) :
    binomialExpectation p n f ≤ binomialExpectation p n g := by
  induction n generalizing f g with
  | zero => exact h 0
  | succ n ih =>
    have left := ih f g h
    have right := ih (fun k => f (k+1)) (fun k => g (k+1)) (fun k => h (k+1))
    simp only [binomialExpectation]
    have nonnegative : 0 ≤ 1-p := by grind
    have hleft := Rat.mul_le_mul_of_nonneg_left left nonnegative
    have hright := Rat.mul_le_mul_of_nonneg_left right hp
    grind

/-- The expected count of successes is n*p. -/
theorem mean (p : Rat) (n : Nat) :
    binomialExpectation p n (fun (k : Nat) => (k : Rat)) = (n : Rat) * p := by
  induction n with
  | zero => simp [binomialExpectation] <;> grind
  | succ n ih =>
    have shifted : (fun k : Nat => ((k+1 : Nat) : Rat)) = (fun (k : Nat) => (k : Rat) + 1) := by
      funext k
      simp [Rat.natCast_add]
    rw [binomialExpectation, shifted, add, constant, ih]
    simp only [Rat.natCast_add, Rat.natCast_ofNat]
    grind

/-- The second raw moment of the count. -/
theorem secondMoment (p : Rat) (n : Nat) :
    binomialExpectation p n (fun (k : Nat) => (k : Rat)*(k : Rat)) =
      (n : Rat)*p*(1-p) + ((n : Rat)*p)*((n : Rat)*p) := by
  induction n with
  | zero => simp [binomialExpectation] <;> grind
  | succ n ih =>
    have shifted : (fun k : Nat => ((k+1 : Nat) : Rat)*((k+1 : Nat) : Rat)) =
        (fun (k : Nat) => ((k : Rat)*(k : Rat) + 2*(k : Rat)) + 1) := by
      funext k
      simp only [Rat.natCast_add, Rat.natCast_ofNat]
      grind
    rw [binomialExpectation, shifted, add, add, scale, constant, mean, ih]
    simp only [Rat.natCast_add, Rat.natCast_ofNat]
    grind

/-- The count has variance n*p*(1-p), derived from the sampling law. -/
theorem variance (p : Rat) (n : Nat) :
    binomialExpectation p n (fun (k : Nat) => ((k : Rat)-(n : Rat)*p)*((k : Rat)-(n : Rat)*p)) =
      (n : Rat)*p*(1-p) := by
  have expansion : (fun k : Nat => ((k : Rat)-(n : Rat)*p)*((k : Rat)-(n : Rat)*p)) =
      (fun (k : Nat) => ((k : Rat)*(k : Rat) + (-2*(n : Rat)*p)*(k : Rat)) + ((n : Rat)*p)*((n : Rat)*p)) := by
    funext k
    grind
  rw [expansion, add, add, scale, constant, mean, secondMoment]
  grind

/-- A square is nonnegative over the rationals. -/
theorem square_nonnegative (x : Rat) : 0 ≤ x*x := by
  by_cases h : 0 ≤ x
  · exact Rat.mul_nonneg h h
  · have hn : 0 ≤ -x := by grind
    have hsq := Rat.mul_nonneg hn hn
    grind

/-- Every Bernoulli variable has variance at most one quarter. -/
theorem bernoulli_variance_bound (p : Rat) : p*(1-p) ≤ 1/4 := by
  have h := square_nonnegative (p-1/2)
  grind

/-- The probability that the empirical frequency misses p by more than epsilon. -/
def errorProbability (p epsilon : Rat) (n : Nat) : Rat :=
  binomialExpectation p n fun k =>
    if (n : Rat)*epsilon < (k : Rat)-(n : Rat)*p ∨
       (k : Rat)-(n : Rat)*p < -(n : Rat)*epsilon then 1 else 0

/-- A finite-sample confidence theorem, with its variance bound proved above.
Choose n and epsilon so that n/4 ≤ delta*(n*epsilon)^2. -/
theorem confidence
    (p epsilon delta : Rat) (n : Nat)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (he : 0 < epsilon)
    (budget : (n : Rat)/4 ≤ delta * (((n : Rat)*epsilon)*((n : Rat)*epsilon))) :
    errorProbability p epsilon n ≤ delta := by
  have npos : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr hn
  have sizepos : 0 < (n : Rat)*epsilon := Rat.mul_pos npos he
  have thresholdPos : 0 < ((n : Rat)*epsilon)*((n : Rat)*epsilon) := by
    exact Rat.mul_pos (Rat.mul_pos npos he) (Rat.mul_pos npos he)
  have pointwise : ∀ k : Nat,
      (((n : Rat)*epsilon)*((n : Rat)*epsilon)) *
        (if (n : Rat)*epsilon < (k : Rat)-(n : Rat)*p ∨
          (k : Rat)-(n : Rat)*p < -(n : Rat)*epsilon then (1 : Rat) else 0) ≤
        ((k : Rat)-(n : Rat)*p)*((k : Rat)-(n : Rat)*p) := by
    intro k
    split
    · next h =>
      rcases h with h | h
      · have hprod := Rat.mul_nonneg
          (show 0 ≤ ((k : Rat)-(n : Rat)*p) - (n : Rat)*epsilon by grind)
          (show 0 ≤ ((k : Rat)-(n : Rat)*p) + (n : Rat)*epsilon by grind)
        grind
      · have hprod := Rat.mul_nonneg
          (show 0 ≤ -((k : Rat)-(n : Rat)*p) - (n : Rat)*epsilon by grind)
          (show 0 ≤ -((k : Rat)-(n : Rat)*p) + (n : Rat)*epsilon by grind)
        grind
    · have h := square_nonnegative ((k : Rat)-(n : Rat)*p)
      grind
  have h := monotone p hp hp1 n _ _ pointwise
  rw [scale, variance] at h
  change (((n : Rat)*epsilon)*((n : Rat)*epsilon)) * errorProbability p epsilon n ≤
    (n : Rat)*p*(1-p) at h
  have vb := Rat.mul_le_mul_of_nonneg_left (bernoulli_variance_bound p)
    (show (0 : Rat) ≤ (n : Rat) by grind)
  have bound : (((n : Rat)*epsilon)*((n : Rat)*epsilon)) * errorProbability p epsilon n ≤
      (((n : Rat)*epsilon)*((n : Rat)*epsilon)) * delta := by grind
  exact Rat.le_of_mul_le_mul_left bound thresholdPos

/-- Acceptance requires the entire error interval to fit, with clipping to [0,1]. -/
def acceptsCount (target tolerance epsilon : Rat) (n k : Nat) : Prop :=
  (target - tolerance ≤ 0 ∨ (n : Rat)*(target - tolerance + epsilon) ≤ (k : Rat)) ∧
  (1 ≤ target + tolerance ∨ (k : Rat) ≤ (n : Rat)*(target + tolerance - epsilon))

instance (target tolerance epsilon : Rat) (n k : Nat) :
    Decidable (acceptsCount target tolerance epsilon n k) := by
  unfold acceptsCount
  infer_instance

/-- Probability of accepting a constraint whose true probability is outside its band. -/
def falseAcceptance (p target tolerance epsilon : Rat) (n : Nat) : Rat :=
  binomialExpectation p n fun k =>
    if acceptsCount target tolerance epsilon n k ∧ ¬ WithinTolerance p target tolerance then 1 else 0

/-- A falsely accepted constraint entails an estimation error larger than epsilon. -/
theorem false_accept_implies_error (p target tolerance epsilon : Rat) (n k : Nat)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    (accepted : acceptsCount target tolerance epsilon n k)
    (unfair : ¬ WithinTolerance p target tolerance) :
    (n : Rat)*epsilon < (k : Rat)-(n : Rat)*p ∨
      (k : Rat)-(n : Rat)*p < -(n : Rat)*epsilon := by
  have npos : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr hn
  unfold acceptsCount at accepted
  unfold WithinTolerance at unfair
  by_cases low : p < target - tolerance
  · have edge : (n : Rat)*p < (n : Rat)*(target-tolerance) :=
      Rat.mul_lt_mul_of_pos_left low npos
    grind
  · have high : target+tolerance < p := by grind
    have edge : (n : Rat)*(target+tolerance) < (n : Rat)*p :=
      Rat.mul_lt_mul_of_pos_left high npos
    grind

/-- Rigorous statistical fairness theorem: the risk of false acceptance is at most delta.
This is a probability of error under independent sampling, not `isFair` inferred from one sample. -/
theorem fairnessConfidence (p target tolerance epsilon delta : Rat) (n : Nat)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (he : 0 < epsilon)
    (budget : (n : Rat)/4 ≤ delta * (((n : Rat)*epsilon)*((n : Rat)*epsilon))) :
    falseAcceptance p target tolerance epsilon n ≤ delta := by
  have h : falseAcceptance p target tolerance epsilon n ≤ errorProbability p epsilon n := by
    apply monotone p hp hp1 n
    intro k
    split
    · next h =>
      have err := false_accept_implies_error p target tolerance epsilon n k hp hp1 hn h.1 h.2
      simp only [ite_eq_left err]
      exact Rat.le_refl
    · split <;> decide +kernel
  exact Rat.le_trans h (confidence p epsilon delta n hp hp1 hn he budget)

/-- Exact expectation under a finite joint observation law. -/
def expectation (law : Distribution α) (f : α → Rat) : Rat :=
  (law.entries.map fun (x, weight) => weight * f x).sum

/-- Nonnegative weights preserve pointwise comparisons of joint events. -/
theorem expectation_monotone (law : Distribution α)
    (nonnegative : ∀ e ∈ law.entries, 0 ≤ e.2)
    (f g : α → Rat) (h : ∀ x, f x ≤ g x) : expectation law f ≤ expectation law g := by
  unfold expectation
  generalize law.entries = entries at *
  revert nonnegative
  induction entries with
  | nil => intro _; exact Rat.le_refl
  | cons e rest ih =>
    intro nonnegative
    have hp := nonnegative e (by simp)
    have ht : ∀ e ∈ rest, 0 ≤ e.2 := by
      intro e he
      exact nonnegative e (by simp [he])
    have hr := ih ht
    have he := Rat.mul_le_mul_of_nonneg_left (h e.1) hp
    simp only [List.map_cons, List.sum_cons]
    grind

/-- A constraint's target and absolute tolerance. -/
structure Band where
  target : Rat
  tolerance : Rat

/-- True fairness of every tested constraint. -/
def familyFair (truth : Fin m → Rat) (bands : Fin m → Band) : Prop :=
  ∀ i, WithinTolerance (truth i) (bands i).target (bands i).tolerance

/-- Every constraint must pass; selecting only favorable rows is not permitted. -/
def acceptsFamily (bands : Fin m → Band) (epsilon : Rat) (n : Nat) (counts : Fin m → Nat) : Prop :=
  ∀ i, acceptsCount (bands i).target (bands i).tolerance epsilon n (counts i)

instance (truth : Fin m → Rat) (bands : Fin m → Band) : Decidable (familyFair truth bands) := by
  unfold familyFair
  infer_instance

instance (bands : Fin m → Band) (epsilon : Rat) (n : Nat) (counts : Fin m → Nat) :
    Decidable (acceptsFamily bands epsilon n counts) := by
  unfold acceptsFamily
  infer_instance

/-- The probability of incorrectly accepting the entire family under a joint law. -/
def familyFalseAcceptance (law : Distribution (Fin m → Nat)) (truth : Fin m → Rat)
    (bands : Fin m → Band) (epsilon : Rat) (n : Nat) : Rat :=
  expectation law fun counts =>
    if acceptsFamily bands epsilon n counts ∧ ¬ familyFair truth bands then 1 else 0

/-- An explicit sampling-model hypothesis: each row contains n independent Bernoulli trials.
Rows may be correlated with one another. This is NOT an assumed confidence bound. -/
def BinomialMarginals (law : Distribution (Fin m → Nat)) (truth : Fin m → Rat) (n : Nat) : Prop :=
  ∀ i f, expectation law (fun counts => f (counts i)) = binomialExpectation (truth i) n f

/-- Rigorous family-wise fairness-confidence theorem.
If all rows must pass, any unfair row bounds the probability of false certification;
no independence between rows or post-hoc choice of a favorable row is assumed. -/
theorem familyFairnessConfidence
    (law : Distribution (Fin m → Nat)) (truth : Fin m → Rat) (bands : Fin m → Band)
    (epsilon delta : Rat) (n : Nat)
    (valid : law.Valid) (sampling : BinomialMarginals law truth n)
    (probabilities : ∀ i, 0 ≤ truth i ∧ truth i ≤ 1)
    (hn : 0 < n) (he : 0 < epsilon) (hd : 0 ≤ delta)
    (budget : (n : Rat)/4 ≤ delta * (((n : Rat)*epsilon)*((n : Rat)*epsilon))) :
    familyFalseAcceptance law truth bands epsilon n ≤ delta := by
  by_cases fair : familyFair truth bands
  · have h : familyFalseAcceptance law truth bands epsilon n ≤ expectation law (fun _ => 0) := by
      apply expectation_monotone law valid.1
      intro counts
      simp only [fair, not_true_eq_false, and_false, ite_false]
      exact Rat.le_refl
    have zero : expectation law (fun _ => 0) = 0 := by
      unfold expectation
      induction law.entries with
      | nil => rfl
      | cons e rest ih =>
        change (rest.map fun e => e.2 * 0).sum = 0 at ih
        change e.2 * 0 + (rest.map fun e => e.2 * 0).sum = 0
        rw [ih, Rat.mul_zero, Rat.zero_add]
    rw [zero] at h
    exact Rat.le_trans h hd
  · obtain ⟨i, unfair⟩ := Classical.not_forall.mp fair
    have h : familyFalseAcceptance law truth bands epsilon n ≤
        expectation law (fun counts =>
          if acceptsCount (bands i).target (bands i).tolerance epsilon n (counts i) ∧
            ¬ WithinTolerance (truth i) (bands i).target (bands i).tolerance then 1 else 0) := by
      apply expectation_monotone law valid.1
      intro counts
      split
      · next ha =>
        have hi := ha.1 i
        simp only [hi, unfair]
        exact Rat.le_refl
      · split <;> decide +kernel
    rw [sampling i (fun k =>
      if acceptsCount (bands i).target (bands i).tolerance epsilon n k ∧
        ¬ WithinTolerance (truth i) (bands i).target (bands i).tolerance then 1 else 0)] at h
    exact Rat.le_trans h (fairnessConfidence (truth i) (bands i).target (bands i).tolerance
      epsilon delta n (probabilities i).1 (probabilities i).2 hn he budget)

/-- The fixed confidence level used for new audits: false acceptance at most 0.1%. -/
def confidenceDelta : Rat := 1 / 1000

/-- Fixed frequency-error allowance, chosen before the held-out validation run. -/
def confidenceEpsilon : Rat := 1 / 25

/-- Required qualifying observations per constraint, not merely total games. -/
def confidenceSamples : Nat := 160000

/-- The chosen sample size meets the proved confidence budget using exact arithmetic. -/
theorem confidenceBudget : (confidenceSamples : Rat)/4 ≤ confidenceDelta *
    (((confidenceSamples : Rat)*confidenceEpsilon)*((confidenceSamples : Rat)*confidenceEpsilon)) := by
  decide +kernel

end Rpg.Probability.Confidence
