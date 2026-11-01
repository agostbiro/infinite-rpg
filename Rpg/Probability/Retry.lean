import Rpg.Probability.StatisticalAdmission

/-! Repeated proposals must not obtain admission just by rerolling the test.
Attempt n spends half the remaining error allowance. The theorem covers any finite,
adaptive sequence under the binomial assumptions at each history. -/
namespace Rpg.Probability
open Confidence

/-- The remaining error allowance after `n` validation attempts. -/
def remainingRisk : Nat → Rat
  | 0 => confidenceDelta
  | n+1 => remainingRisk n / 2

/-- One validation spends half the remaining allowance. -/
def attemptRisk (n : Nat) : Rat := remainingRisk (n+1)

/-- Every finite attempt has a positive error allowance no larger than the shared allowance. -/
theorem remainingRisk_valid (n : Nat) : 0 < remainingRisk n ∧ remainingRisk n ≤ confidenceDelta := by
  induction n with
  | zero => exact ⟨confidenceLevel_valid.1, Rat.le_refl⟩
  | succ n ih =>
    simp only [remainingRisk]
    grind

/-- A finite adaptive validation tree. A new candidate may depend on all earlier counts. -/
inductive RetryTree : Nat → Type where
  | stop {n : Nat} : RetryTree n
  | attempt {n : Nat} (candidate : StatisticalCandidate)
      (law : Distribution (Fin (candidate.horizon+1) → Observation))
      (next : (Fin (candidate.horizon+1) → Observation) → RetryTree n) : RetryTree (n+1)

/-- The sampling assumption is required at every history, before drawing that attempt's batch. -/
def RetryTree.Valid : {n : Nat} → RetryTree n → Prop
  | _, .stop => True
  | _, .attempt a law next =>
    law.Valid ∧ Nonempty (BinomialSampling law a.truth) ∧
    (∀ i, 0 ≤ a.truth i ∧ a.truth i ≤ 1) ∧ ∀ obs, (next obs).Valid

/-- Probability of any false acceptance in a finite tree, including later requests after success. -/
def RetryTree.falseAcceptance : {n : Nat} → RetryTree n → Nat → Rat
  | _, .stop, _ => 0
  | _, .attempt a law next, index => expectation law fun obs =>
    if acceptsFamily a.bands (attemptRisk index) obs ∧ ¬ familyFair a.truth a.bands then 1
    else (next obs).falseAcceptance (index+1)

/-- Finite expectation distributes over addition. -/
private theorem expectation_add (law : Distribution α) (f g : α → Rat) :
    expectation law (fun x => f x + g x) = expectation law f + expectation law g := by
  unfold expectation
  induction law.entries with
  | nil =>
    change (0 : Rat) = 0 + 0
    decide +kernel
  | cons e rest ih =>
    simp only [List.map_cons, List.sum_cons] at *
    grind

/-- Adaptive retries preserve the remaining confidence budget; no independence between rows
or between chosen candidates is assumed. Fresh conditional-binomial batches are required. -/
theorem RetryTree.fair {n : Nat} (tree : RetryTree n) (start : Nat)
    -- Each conditional batch obeys the same explicit sampling model as the main fairness theorem.
    (valid : tree.Valid) : tree.falseAcceptance start ≤ remainingRisk start := by
  induction tree generalizing start with
  | stop => exact Rat.le_of_lt (remainingRisk_valid start).1
  | @attempt n a law next ih =>
    obtain ⟨lawValid, ⟨sampling⟩, probabilities, children⟩ := valid
    have tail0 := Rat.le_of_lt (remainingRisk_valid (start+1)).1
    have first := (a.fairAt (attemptRisk start) tail0 law lawValid sampling probabilities).2
    have bound := expectation_monotone law lawValid.1
      (fun obs => if acceptsFamily a.bands (attemptRisk start) obs ∧ ¬ familyFair a.truth a.bands then 1
        else (next obs).falseAcceptance (start+1))
      (fun obs => (if acceptsFamily a.bands (attemptRisk start) obs ∧
        ¬ familyFair a.truth a.bands then 1 else 0) + remainingRisk (start+1)) (by
        intro obs
        have tail := ih obs (start+1) (children obs)
        split <;> simp_all <;> grind)
    rw [expectation_add, expectation_constant law lawValid] at bound
    change familyFalseAcceptance law a.truth a.bands (attemptRisk start) ≤ attemptRisk start at first
    change expectation law _ ≤ remainingRisk start
    unfold familyFalseAcceptance at first
    simp only [attemptRisk, remainingRisk] at first bound ⊢
    grind

end Rpg.Probability
