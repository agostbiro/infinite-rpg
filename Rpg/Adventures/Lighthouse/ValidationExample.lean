import Rpg.Adventures.Lighthouse.Confidence

/-! The counts of the 1,000 Lighthouse games with the fixed validation seed. The build fails if
the games give other counts. The server still plays the games again at start-up; these
recorded counts do not admit the Lighthouse. -/
namespace Rpg.Lighthouse
open Probability Probability.Confidence

/-- Recorded counts at seed 20261103, with no unresolved outcomes inside the window.
They changed when Mara got her broadsword back, the model's Player started to pick maneuvers,
the curve became shape 2 (q = 19/20, tolerance 1/5), and the horizon became 5. -/
def recordedValidation : ValidationCounts :=
  ⟨#[1000, 1000, 1000, 1000, 946, 666],
   #[0, 0, 22, 148, 346, 130], 1000, false⟩

/-- The same games with no deaths at all: an Adventure that is too easy. -/
def noDeaths : ValidationCounts :=
  { recordedValidation with deaths := #[0, 0, 0, 0, 0, 0] }

-- The check rejects an Adventure where the Character never dies: rows 3 to 5 have a lower edge above 0.
#guard !decide (ValidationAccepted statisticalCandidate.horizon noDeaths)

-- Runtime regression checks are distinct from the kernel-proved coverage theorem.
#guard decide (ValidationAccepted statisticalCandidate.horizon recordedValidation)
#guard let observed := validateCounts statisticalCandidate
  observed.trials == recordedValidation.trials &&
  observed.deaths == recordedValidation.deaths &&
  observed.games == recordedValidation.games &&
  observed.aborted == recordedValidation.aborted

end Rpg.Lighthouse
