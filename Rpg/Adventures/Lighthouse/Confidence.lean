import Rpg.Adventures.Lighthouse.Definition
import Rpg.Probability.StatisticalAdmission

namespace Rpg.Lighthouse

/-- Remaining scene-choice bound, derived from this story's actual links. -/
def sceneRank : SceneId → Nat
  | 0 => 6
  | 1 => 5
  | 2 => 3
  | 3 => 4
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | _ => 0

/-- Every possible story link decreases the rank, independent of combat odds or HP. -/
theorem ranks_decrease : Probability.DecreasingRanks lighthouse sceneRank := by
  unfold Probability.DecreasingRanks
  decide

/-- Lighthouse's source-bound, finite-route statistical experiment. -/
def statisticalCandidate : Probability.StatisticalCandidate where
  toAdventureDefinition := lighthouseDefinition
  rank := sceneRank
  decreasing := ranks_decrease
  horizonPositive := by decide

/-- The route bound is a kernel proof, not an observed maximum from sampled games. -/
theorem route_bound (walk : Probability.SceneWalk lighthouse lighthouse.start length last) : length ≤ 6 := by
  have h := Probability.sceneWalk_bound ranks_decrease walk
  change length + sceneRank last ≤ 6 at h
  omega

/-- Lighthouse's statistical fairness theorem under the explicit independent-sampling model.
The theorem bounds false acceptance of its graph's tested probabilities by 0.1%. -/
theorem lighthouse_fairnessConfidence
    (law : Probability.Distribution (Fin (statisticalCandidate.horizon+1) → Nat))
    (valid : law.Valid)
    (sampling : Probability.Confidence.BinomialMarginals law statisticalCandidate.truth
      Probability.Confidence.confidenceSamples)
    (probabilities : ∀ i, 0 ≤ statisticalCandidate.truth i ∧ statisticalCandidate.truth i ≤ 1) :
    Probability.Confidence.familyFalseAcceptance law statisticalCandidate.truth
      (Probability.confidenceBands statisticalCandidate.horizon)
      Probability.Confidence.confidenceEpsilon Probability.Confidence.confidenceSamples ≤
      Probability.Confidence.confidenceDelta :=
  statisticalCandidate.fairnessConfidence law valid sampling probabilities

end Rpg.Lighthouse
