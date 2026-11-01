import Rpg.Adventures.Lighthouse.Confidence

/-! Regression data for the fixed 1,000-game batch. Runtime admission regenerates
its observations; this record cannot replace source-bound evidence. -/
namespace Rpg.Lighthouse
open Probability Probability.Confidence

/-- Recorded counts at seed 20261103, with no unresolved outcomes inside the window. -/
def recordedValidation : ValidationCounts :=
  ⟨#[1000, 1000, 1000, 1000, 967, 679, 177],
   #[0, 0, 0, 40, 95, 33, 0], 1000, false⟩

-- Runtime regression checks are distinct from the kernel-proved coverage theorem.
#guard decide (ValidationAccepted statisticalCandidate.horizon recordedValidation)
#guard let observed := validateCounts statisticalCandidate
  observed.trials == recordedValidation.trials &&
  observed.deaths == recordedValidation.deaths &&
  observed.games == recordedValidation.games &&
  observed.aborted == recordedValidation.aborted

end Rpg.Lighthouse
