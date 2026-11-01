import Rpg.Probability.StatisticalAdmission
import Rpg.Adventures.Harbor

namespace Rpg.Probability.Confidence

/-- A concrete, nonzero failure risk is bounded by the proved theorem without enumerating 2^n samples. -/
example : falseAcceptance (1/2) (4/25) (1/5) confidenceEpsilon confidenceSamples ≤ confidenceDelta :=
  falseAcceptance_bound _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
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

theorem zeroLaw_valid : zeroLaw.Valid := by
  simp [zeroLaw, Distribution.Valid, pure, Pure.pure]
  decide +kernel

theorem zeroLaw_sampling : BinomialMarginals zeroLaw (fun _ => 0) confidenceSamples := by
  intro i f
  rw [zero_sampling]
  change (1 : Rat) * f 0 + 0 = f 0
  rw [Rat.one_mul, Rat.add_zero]

/-- An all-zero observation vector is not sufficient without the required trial counts. -/
example : ¬ ValidationAccepted 1 ⟨#[0, 0], #[0, 0], 0, false⟩ := by decide +kernel

/-- Even otherwise acceptable counts cannot be admitted after censoring. -/
example : ¬ ValidationAccepted 1 ⟨#[confidenceSamples, confidenceSamples], #[0, 0], confidenceSamples, true⟩ := by decide +kernel

/-- Rational endpoints retain the full four-percentage-point error allowance. -/
example : confidenceInterval confidenceEpsilon confidenceSamples 43753 =
    ⟨37353/160000, 50153/160000⟩ := by decide +kernel

/-- Clipping changes only the endpoints outside the probability range. -/
example : confidenceInterval confidenceEpsilon confidenceSamples 0 = ⟨0, 1/25⟩ := by decide +kernel
example : confidenceInterval confidenceEpsilon confidenceSamples confidenceSamples =
    ⟨24/25, 1⟩ := by decide +kernel

/-- An accepted estimate's whole interval fits the shared Weibull band. -/
example : (4/25 : Rat) - 1/5 ≤
      (confidenceInterval confidenceEpsilon confidenceSamples 43753).lower ∧
    (confidenceInterval confidenceEpsilon confidenceSamples 43753).upper ≤ 4/25 + 1/5 :=
  accepted_interval _ _ _ _ _ (by decide) (by decide +kernel)

/-- An unresolved last tested death outcome prevents finite admission. -/
example : observationsComplete 6 ⟨.censored, 7⟩ = false := by decide

/-- An unresolved outcome after the last tested death turn is outside the window. -/
example : observationsComplete 6 ⟨.censored, 8⟩ = true := by decide
example : observationsComplete 6 ⟨.invalid, 8⟩ = false := by decide

/-- A loop can be observed finitely without any termination or rank proof. -/
def loopStory : Adventure :=
  { title := "Finite loop fixture", start := 0, scenes := [
    { id := 0, title := "Loop", text := "", choices := [
      { text := "Again", outcome := .goto 0 },
      { text := "End", outcome := .goto 1 }] },
    { id := 1, title := "End", text := "", choices := [] } ] }

/-- The candidate type accepts a legal cycle with a positive finite comparison window. -/
def loopCandidate : StatisticalCandidate where
  rules := Harbor.rules
  hero := Harbor.iona
  heroLegal := Harbor.iona_legal
  story := loopStory
  legal := check_sound (by decide +kernel)
  horizon := 2
  horizonPositive := by decide

/-- Harbor's graph gives a concrete sampling model with every hypothesis discharged. -/
theorem harbor_truth_zero : ∀ i, Harbor.statisticalCandidate.truth i = 0 := by decide +kernel

/-- The main finite theorem applies to a real adventure and a valid joint sampling law. -/
example :
    (∀ i, intervalMissProbability zeroLaw Harbor.statisticalCandidate.truth
      confidenceEpsilon confidenceSamples i ≤ confidenceDelta) ∧
    familyFalseAcceptance zeroLaw Harbor.statisticalCandidate.truth (confidenceBands 1)
      confidenceEpsilon confidenceSamples ≤ confidenceDelta := by
  apply Harbor.fair zeroLaw zeroLaw_valid
  -- The model's row marginals use Harbor's actual graph probabilities.
  · intro i f
    rw [harbor_truth_zero]
    exact zeroLaw_sampling i f
  -- Those graph probabilities lie in the probability range.
  · intro i
    rw [harbor_truth_zero]
    decide +kernel

end Rpg.Probability.Confidence
