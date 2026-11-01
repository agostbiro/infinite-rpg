import Rpg.Adventures.Lighthouse.Definition
import Rpg.Probability.StatisticalAdmission

namespace Rpg.Lighthouse

/-- Fixed comparison window: first-turn death and conditional deaths for 0 ≤ t < 6. -/
def fairnessHorizon : Nat := 6

/-- Lighthouse's rules, character, story, and preselected finite comparison window. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := lighthouseDefinition
  horizon := fairnessHorizon
  horizonPositive := by decide

/-- Lighthouse's finite confidence intervals and Weibull comparisons satisfy the fairness theorem. -/
theorem fair : Probability.Fair statisticalCandidate := statisticalCandidate.fair

end Rpg.Lighthouse
