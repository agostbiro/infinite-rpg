import Rpg.Adventures.TestAdventure.Confidence

namespace Rpg

/-- The Adventures in this repo, for the balance screen (`screen.lean`): now only the test
Adventure. A new built-in Adventure goes here too (see `docs/follow-ups.md`). -/
def statisticalCandidates : List Probability.StatisticalCandidate :=
  [TestAdventure.statisticalCandidate]

end Rpg
