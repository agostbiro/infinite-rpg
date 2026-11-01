import Rpg.Adventures.Lafayette.Definition
import Rpg.Probability.StatisticalAdmission

namespace Rpg.Lafayette

/-- The balance check looks at death on turn 1, and at death on turn t+2 for 0 ≤ t < 5. -/
def balanceHorizon : Nat := 5

/-- The built-in Adventure as a candidate for the balance check, with horizon 5. Like every
Adventure, it uses the default curve. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := barrenHillDefinition
  horizon := balanceHorizon
  horizonPositive := by decide

/-- The balance theorem `balanced`, applied to the built-in Adventure. It is about the test, not
a proof that the Adventure is balanced: the run-time check admits it, and the server runs that
check at start-up. -/
theorem balanced : Probability.Balanced statisticalCandidate := statisticalCandidate.balanced

end Rpg.Lafayette
