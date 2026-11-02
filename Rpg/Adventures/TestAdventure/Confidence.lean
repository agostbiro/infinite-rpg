import Rpg.Adventures.TestAdventure.Definition
import Rpg.Probability.StatisticalAdmission

namespace Rpg.TestAdventure

/-- The balance check looks at death on turn 1, and at death on turn t+2 for 0 ≤ t < 5. -/
def balanceHorizon : Nat := 5

/-- The test Adventure as a candidate for the balance check, with horizon 5. Like every
Adventure, it uses the default curve. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := testAdventureDefinition
  horizon := balanceHorizon
  horizonPositive := by decide

/-- The balance theorem `balanced`, applied to the test Adventure. It is about the test, not a
proof that the test Adventure is balanced: the run-time check admits it. -/
theorem balanced : Probability.Balanced statisticalCandidate := statisticalCandidate.balanced

end Rpg.TestAdventure
