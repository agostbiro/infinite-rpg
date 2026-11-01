import Rpg.Adventures.Lighthouse.Definition
import Rpg.Probability.StatisticalAdmission

namespace Rpg.Lighthouse

/-- The balance check looks at death on turn 1, and at death on turn t+2 for 0 ≤ t < 5. -/
def balanceHorizon : Nat := 5

/-- The Lighthouse as a candidate for the balance check, with horizon 5. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := lighthouseDefinition
  horizon := balanceHorizon
  horizonPositive := by decide

/-- The balance theorem `balanced`, applied to the Lighthouse candidate. It is about the test, not a
proof that the Lighthouse is balanced: the run-time check admits it. -/
theorem balanced : Probability.Balanced statisticalCandidate := statisticalCandidate.balanced

end Rpg.Lighthouse
