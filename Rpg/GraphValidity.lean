import Rpg.EventGraph
import Rpg.Probability.StatisticalAdmission

/-! Graph validity combines structural legality, the event-cycle restriction and
the statistical balance test. It does not assert that sampling proves true probabilities. -/
namespace Rpg
open Probability

/-- Validity is relative to a hero, rules, policy, horizon, seed and observed batch. -/
def GraphValid (a : StatisticalCandidate) (seed : Nat) (counts : ValidationCounts) : Prop :=
  LegalCharacter a.rules a.hero ∧
  LegalAdventure a.rules a.hero a.story ∧
  a.story.NoShortCycles ∧
  counts = sampleCounts a seed (validationGamesFor a.policy) ∧
  ValidationAccepted a.horizon counts a.policy

/-- The result of the graph validity test, with its source-bound balance certificate. -/
structure ValidatedGraph where
  statistical : StatisticalAdventure
  eventCycles : statistical.candidate.story.NoShortCycles

/-- An accepted graph satisfies legality, event structure and the balance test together. -/
theorem ValidatedGraph.balanced (g : ValidatedGraph) :
    GraphValid g.statistical.candidate g.statistical.seed g.statistical.counts := by
  exact ⟨g.statistical.candidate.heroLegal, g.statistical.candidate.legal,
    g.eventCycles, g.statistical.provenance, g.statistical.accepted⟩

/-- Check event structure and balance on the same candidate used by the game engine. -/
def validateGraph (a : StatisticalCandidate) (seed : Nat) :
    Except (List String) ValidatedGraph :=
  if hc : a.story.NoShortCycles then
    let counts := sampleCounts a seed (validationGamesFor a.policy)
    if accepted : ValidationAccepted a.horizon counts a.policy then
      .ok ⟨⟨a, a.fair, seed, counts, rfl, accepted⟩, hc⟩
    else .error ((failedRows a.horizon counts a.policy).map ("fairness: " ++ ·))
  else .error a.story.eventCycleErrors

end Rpg
