import Rpg.Probability.StatisticalAdmission

/-! Cheap exploratory data selects proposals only. It is never admission evidence. -/
namespace Rpg.Probability

/-- Screening uses few runs and no exact interval inversion. Validation uses an independent seed. -/
def screenGames : Nat := 256

/-- Only adequately observed rows can reject a proposal at the exploratory stage.
A sparse row proceeds to validation; it is not assumed safe. -/
def StatisticalCandidate.screenFailures (a : StatisticalCandidate) (c : ValidationCounts) : List String :=
  (if c.aborted then ["A screening trajectory exceeded the combat limit."] else []) ++
  (List.finRange (a.horizon + 1)).filterMap fun i =>
    let obs := c.observation i.val
    if obs.trials < 32 then none else
    let estimate := (obs.deaths : Rat) / obs.trials
    let band := a.bands i
    if WithinTolerance estimate band.target band.tolerance then none else
      some s!"Screen row {i.val}: {obs.deaths}/{obs.trials} deaths, target {band.target}. Revise this encounter; final confidence validation is still required."

/-- A permissive screen cannot install a proposal; the caller still needs an Admission certificate. -/
def StatisticalCandidate.screenPlausible (a : StatisticalCandidate) (c : ValidationCounts) : Bool :=
  a.screenFailures c |>.isEmpty

end Rpg.Probability
