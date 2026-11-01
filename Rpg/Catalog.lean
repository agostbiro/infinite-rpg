import Rpg.Adventures.Harbor
import Rpg.Adventures.Lighthouse.Confidence

/-! Exact certificates are available at build time. Statistical candidates must
complete the source-bound confidence protocol before entering the runtime menu. -/
namespace Rpg

/-- Adding a playable adventure requires its legality and default-policy fairness proofs. -/
def playableAdventures : List Probability.CertifiedAdventure := [Harbor.harborCertified]

/-- Candidates are not playable until `admitStatistically` returns their evidence. -/
def statisticalCandidates : List Probability.StatisticalCandidate := [Lighthouse.statisticalCandidate]

end Rpg
