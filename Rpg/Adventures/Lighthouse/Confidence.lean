import Rpg.Adventures.Lighthouse.Definition
import Rpg.Probability.StatisticalAdmission

namespace Rpg.Lighthouse

/-- The fairness check looks at death on turn 1, and at death on turn t+2 for 0 ≤ t < 5. -/
def fairnessHorizon : Nat := 5

/-- The Lighthouse as a candidate for the fairness check, with horizon 5. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := lighthouseDefinition
  horizon := fairnessHorizon
  horizonPositive := by decide

/-- The fairness theorem `fair`, applied to the Lighthouse candidate. It is about the test, not a
proof that the Lighthouse is fair: the run-time check admits it. -/
theorem fair : Probability.Fair statisticalCandidate := statisticalCandidate.fair

end Rpg.Lighthouse
