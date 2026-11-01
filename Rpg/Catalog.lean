import Rpg.Adventures.Lighthouse.Confidence

namespace Rpg

/-- The built-in Adventures, for the balance screen (`screen.lean`). Each must pass the balance
check before play. -/
def statisticalCandidates : List Probability.StatisticalCandidate :=
  [Lighthouse.statisticalCandidate]

end Rpg
