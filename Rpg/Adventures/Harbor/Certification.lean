import Rpg.Adventures.Harbor.Story
import Rpg.Probability.StatisticalAdmission

namespace Rpg.Harbor

/-- Harbor's own rules, character, story, and legality proofs. -/
def harborDefinition : Probability.AdventureDefinition :=
  ⟨rules, iona, iona_legal, harbor, harbor_legal⟩

/-- Harbor compares first-turn death and death at turn two given activity at turn zero. -/
def fairnessHorizon : Nat := 1

/-- Harbor uses the same finite confidence protocol as other adventures. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := harborDefinition
  horizon := fairnessHorizon
  horizonPositive := by decide

/-- Harbor's finite confidence intervals and Weibull comparisons satisfy the fairness theorem. -/
theorem fair : Probability.Fair statisticalCandidate := statisticalCandidate.fair

end Rpg.Harbor
