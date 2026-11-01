import Rpg.Probability.StatisticalAdmission

namespace Rpg.Probability.Confidence

/-- A concrete, nonzero failure risk is bounded by the proved theorem without enumerating 2^n samples. -/
example : falseAcceptance (1/2) (4/25) (1/5) confidenceEpsilon confidenceSamples ≤ confidenceDelta :=
  fairnessConfidence _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel) confidenceBudget

/-- Clipping at zero permits a genuinely safe first turn. -/
example : acceptsCount (1/5) (1/5) confidenceEpsilon confidenceSamples 0 := by decide +kernel

/-- A certainly lethal first turn cannot pass. -/
example : ¬ acceptsCount (1/5) (1/5) confidenceEpsilon confidenceSamples confidenceSamples := by decide +kernel

/-- Estimates near the policy boundary must leave room for estimation error. -/
example : ¬ acceptsCount (4/25) (1/5) confidenceEpsilon confidenceSamples 56000 := by decide +kernel
example : acceptsCount (4/25) (1/5) confidenceEpsilon confidenceSamples 44000 := by decide +kernel

/-- For p=0, every count is zero. The sampling-model hypotheses have concrete instances. -/
theorem zero_sampling (n : Nat) (f : Nat → Rat) : binomialExpectation 0 n f = f 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [binomialExpectation, ih, Rat.zero_mul, Rat.add_zero]
    have one : (1 - 0 : Rat) = 1 := by decide +kernel
    rw [one, Rat.one_mul]

/-- A valid joint model with perfectly correlated rows; cross-row independence is unnecessary. -/
def zeroLaw : Distribution (Fin 2 → Nat) := pure (fun _ => 0)

example : zeroLaw.Valid := by
  simp [zeroLaw, Distribution.Valid, pure, Pure.pure]
  decide +kernel

example : BinomialMarginals zeroLaw (fun _ => 0) confidenceSamples := by
  intro i f
  rw [zero_sampling]
  change (1 : Rat) * f 0 + 0 = f 0
  rw [Rat.one_mul, Rat.add_zero]

/-- An all-zero observation vector is not sufficient without the required trial counts. -/
example : ¬ ValidationAccepted 1 ⟨#[0, 0], #[0, 0], 0, false⟩ := by decide +kernel

/-- Even otherwise acceptable counts cannot be admitted after censoring. -/
example : ¬ ValidationAccepted 1 ⟨#[confidenceSamples, confidenceSamples], #[0, 0], confidenceSamples, true⟩ := by decide +kernel

end Rpg.Probability.Confidence
