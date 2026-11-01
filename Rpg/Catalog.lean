import Rpg.Adventures.Lighthouse.Confidence

namespace Rpg

/-- The built-in Adventures, for the fairness screen (`screen.lean`). Each must pass the fairness
check before play. -/
def statisticalCandidates : List Probability.StatisticalCandidate :=
  [Lighthouse.statisticalCandidate]

end Rpg
