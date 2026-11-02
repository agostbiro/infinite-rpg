import Rpg.Adventures.TestAdventure.Confidence
import Rpg.Adventures.Lafayette.Confidence

namespace Rpg

/-- The Adventures in this repo, for the balance screen (`screen.lean`): the built-in Adventure,
Lafayette at Barren Hill, and the test Adventure. -/
def statisticalCandidates : List Probability.StatisticalCandidate :=
  [Lafayette.statisticalCandidate, TestAdventure.statisticalCandidate]

end Rpg
