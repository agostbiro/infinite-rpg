import Rpg.Adventures.Lighthouse.Confidence

/-! Kernel-check the numbers from the frozen held-out run. This regression record
has no provenance proof and cannot itself create a `StatisticalAdventure`.
Runtime admission always regenerates source-bound observations. -/
namespace Rpg.Lighthouse
open Probability Probability.Confidence

/-- Recorded validation data from seed 20261102, with no censored or invalid trajectories. -/
def recordedValidation : ValidationCounts :=
  ⟨#[160000, 160000, 160000, 160000, 160000, 160000, 160000],
   #[0, 0, 1374, 16060, 43753, 22175, 0], 979266, false⟩

/-- The held-out numerical acceptance result is checked by the Lean kernel. -/
theorem recorded_validation_passes : ValidationAccepted statisticalCandidate.horizon recordedValidation := by
  decide +kernel

/-- The same observation would not pass the original policy; the relaxation is substantive. -/
example : ¬ acceptsCount ((FairnessPolicy.mk (99/100) 2 (1/20)).deathAtTwo 3)
    (1/20) confidenceEpsilon confidenceSamples 43753 := by decide +kernel

end Rpg.Lighthouse
