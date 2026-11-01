import Rpg.Probability.StatisticalAdmission
import Rpg.Probability.TestStory

namespace Rpg.Probability.Confidence

/-- Exact tails agree with a direct five-coin calculation. -/
example : lowerTail (1/2) 5 1 = 3/16 := by decide +kernel
example : upperTail (1/2) 5 4 = 3/16 := by decide +kernel

/-- No data gives the full probability range and cannot pass admission. -/
example : confidenceInterval confidenceDelta 0 0 = ⟨0, 1⟩ := by decide +kernel
example : ¬ acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨0, 0⟩ := by decide +kernel

/-- Zero observed deaths retains an exact-binomial upper limit. -/
example : confidenceInterval confidenceDelta 10 0 = ⟨0, 79/256⟩ := by decide +kernel

/-- All observed deaths retains an exact-binomial lower limit. -/
example : confidenceInterval confidenceDelta 10 10 = ⟨177/256, 1⟩ := by decide +kernel

/-- A small safe sample can pass the band, but one observation is insufficient. -/
example : acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨10, 0⟩ := by decide +kernel
example : ¬ acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨1, 0⟩ := by decide +kernel

/-- A frequency inside the band is insufficient if its interval extends outside. -/
example : ¬ acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨20, 7⟩ := by decide +kernel
example : acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨20, 2⟩ := by decide +kernel

/-- Certain death and impossible counts cannot pass. -/
example : ¬ acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨10, 10⟩ := by decide +kernel
example : ¬ acceptsCount ⟨4/25, 1/5⟩ confidenceDelta ⟨10, 11⟩ := by decide +kernel

/-- Different target curves can accept or reject the same observed outcomes. -/
example : acceptsCount (confidenceBandsFor ⟨19/20, 2, 1/5⟩ 5 ⟨0, by decide⟩)
    confidenceDelta ⟨20, 0⟩ := by decide +kernel
example : ¬ acceptsCount (confidenceBandsFor ⟨1/2, 2, 1/10⟩ 5 ⟨0, by decide⟩)
    confidenceDelta ⟨20, 0⟩ := by decide +kernel

/-- Higher confidence can reject the same sample because its entire interval must fit. -/
example : acceptsCount ⟨1/20, 1/10⟩ (1/10) ⟨20, 0⟩ := by decide +kernel
example : ¬ acceptsCount ⟨1/20, 1/10⟩ (1/100) ⟨20, 0⟩ := by decide +kernel

/-- An incomplete batch cannot be substituted for the precommitted game count. -/
example : ¬ ValidationAccepted 1 ⟨#[10, 10], #[0, 0], 10, false⟩ confidenceDelta 0
    DifficultyLevel.medium.policy := by decide +kernel
example : ¬ ValidationAccepted 1 ⟨#[1200, 1200], #[0, 0], 1200, true⟩ confidenceDelta 0
    DifficultyLevel.medium.policy := by decide +kernel

/-- Unresolved outcomes inside the tested window abort; later ones do not. -/
example : observationsComplete 6 ⟨.censored, 7⟩ = false := by decide
example : observationsComplete 6 ⟨.censored, 8⟩ = true := by decide
example : observationsComplete 6 ⟨.invalid, 8⟩ = false := by decide

/-- A deterministic Bernoulli law has no deaths for every sample size. -/
theorem zero_sampling (n : Nat) (f : Nat → Rat) : binomialExpectation 0 n f = f 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [binomialExpectation, ih, Rat.zero_mul, Rat.add_zero]
    have one : (1 - 0 : Rat) = 1 := by decide +kernel
    rw [one, Rat.one_mul]

/-- The safe test story has zero true death probability in both tested rows. -/
theorem safe_truth_zero : ∀ i, TestStory.safeCandidate.truth i = 0 := by decide +kernel

/-- The safe story's actual deterministic observation law for the fixed game batch. -/
def zeroLaw : Distribution (Fin (TestStory.safeCandidate.horizon+1) → Observation) := pure (fun _ => ⟨difficultyGames, 0⟩)

/-- A concrete normalized law discharges the main theorem's probability premise. -/
theorem zeroLaw_valid : zeroLaw.Valid := by
  simp [zeroLaw, Distribution.Valid, pure, Pure.pure]
  decide +kernel

/-- The safe story supplies an actual instance of the conditional-binomial sampling model. -/
def zeroLaw_sampling : BinomialSampling zeroLaw TestStory.safeCandidate.truth where
  sizes := fun _ => pure difficultyGames
  sizesValid := by
    intro i
    simp [Distribution.Valid, pure, Pure.pure]
    decide +kernel
  marginals := by
    intro i f
    rw [safe_truth_zero]
    simp [zeroLaw, expectation, pure, Pure.pure, zero_sampling]

/-- Both conclusions of `balanced` hold for a real adventure with all model premises supplied. -/
example :
    (∀ i, intervalMissProbability zeroLaw TestStory.safeCandidate.truth confidenceDelta i ≤ confidenceDelta) ∧
    familyFalseAcceptance zeroLaw TestStory.safeCandidate.truth TestStory.safeCandidate.bands
      confidenceDelta ≤ confidenceDelta := by
  apply TestStory.safeCandidate.balanced zeroLaw zeroLaw_valid zeroLaw_sampling
  intro i
  rw [safe_truth_zero]
  decide +kernel

/-- A nondegenerate joint law has a qualifying count of either one or two. -/
def variableLaw : Distribution (Fin 1 → Observation) := ⟨[
  (fun _ => ⟨1, 0⟩, 1/4), (fun _ => ⟨1, 1⟩, 1/4),
  (fun _ => ⟨2, 0⟩, 1/8), (fun _ => ⟨2, 1⟩, 1/4), (fun _ => ⟨2, 2⟩, 1/8)]⟩

/-- The nondegenerate random-denominator fixture is a normalized probability law. -/
example : variableLaw.Valid := by
  simp [variableLaw, Distribution.Valid]
  decide +kernel

/-- Random qualifying counts still produce binomial deaths conditional on each count. -/
def variable_sampling : BinomialSampling variableLaw (fun _ => 1/2) where
  sizes := fun _ => ⟨[(1, 1/2), (2, 1/2)]⟩
  sizesValid := by
    intro i
    simp [Distribution.Valid]
    decide +kernel
  marginals := by
    intro i f
    simp [variableLaw, expectation, binomialExpectation]
    grind

/-- Coverage integrates over the random denominator without assuming it is fixed. -/
example : intervalMissProbability variableLaw (fun _ => 1/2) confidenceDelta 0 ≤ confidenceDelta :=
  rowConfidence _ _ _ _ variable_sampling (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Rpg.Probability.Confidence

namespace Rpg.Probability
open Confidence

/-- A full batch with games in every row but no deaths at all: an Adventure that is too easy. -/
def noDeathCounts : ValidationCounts :=
  ⟨#[1200, 1200, 1200, 1200, 1135, 800], #[0, 0, 0, 0, 0, 0], 1200, false⟩

-- With horizon 5 (every Wish), the check rejects these counts at every level: on medium,
-- rows 2 to 5 have a lower edge above 0.
#guard DifficultyLevel.all.all fun level =>
  !decide (ValidationAccepted 5 noDeathCounts confidenceDelta 0 level.policy)
-- The same counts with one game too few are rejected for that reason alone, even with no
-- tolerance band to fit (`noBands`).
#guard
  let noBands : BalancePolicy := ⟨1 / 2, 1, 1⟩
  decide (ValidationAccepted 5 noDeathCounts confidenceDelta 0 noBands) &&
    !decide (ValidationAccepted 5 { noDeathCounts with games := 1199 } confidenceDelta 0 noBands)

end Rpg.Probability
