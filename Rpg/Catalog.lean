import Rpg.Adventures.Harbor
import Rpg.Adventures.Lighthouse.Confidence

namespace Rpg

/-- Every adventure must pass its source-bound finite confidence protocol before play. -/
def statisticalCandidates : List Probability.StatisticalCandidate :=
  [Lighthouse.statisticalCandidate, Harbor.statisticalCandidate]

end Rpg
