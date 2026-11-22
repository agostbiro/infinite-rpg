import MarkovRPGCharacters
import MarkovRPGDistributions

/-!
# Character states in finite graphs and correctness of combat projections

Character records contain unbounded natural numbers and lists. We therefore do
not claim that the type of all character states is finite. A particular finite
game graph uses a finite vertex type and attaches complete states to its vertices.

A projection certificate checks transition mass into each reduced-state fiber
and recognition of defeat. From those ONE-STEP conditions we prove preservation
of all finite-horizon and eventual defeat probabilities and existing fairness
predicates. This is not an assumption that an arbitrary combat engine already
satisfies the conditions, nor a proof of almost-sure combat termination.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace MarkovRPG

/-- The existing Markov chain is reused, with complete character/world snapshots
attached to its vertices. A concrete adventure still supplies its transitions. -/
structure CharacterGraph (V Label Scene World : Type*) [Fintype V] where
  rules : Combat.Rules
  chain : MarkovChain V Label
  state : V → GameState Scene World
  state_valid : ∀ v, (state v).WellFormed rules

namespace MarkovChain

variable {V W Label Label' : Type*} [Fintype V] [Fintype W]
variable (M : MarkovChain V Label) (N : MarkovChain W Label')

/-- An exact reduction. Transition probabilities into a reduced vertex are the
sum over its fiber. Defeat must be observable from the reduced state. -/
structure ProjectionCertificate (project : V → W) : Prop where
  initial : project M.initial = N.initial
  defeat : ∀ v, v ∈ M.defeat ↔ project v ∈ N.defeat
  transition : ∀ v w, N.transition (project v) w =
    ∑ u, if project u = w then M.transition v u else 0

namespace ProjectionCertificate

variable {M N} {project : V → W}
variable (cert : M.ProjectionCertificate N project)
include cert

/-- Equal projections have identical next-state distributions on the reduced
graph. This is the precise information-sufficiency requirement. -/
theorem same_project_same_transition {v₁ v₂ : V}
    (h : project v₁ = project v₂) (w : W) :
    (∑ u, if project u = w then M.transition v₁ u else 0) =
      ∑ u, if project u = w then M.transition v₂ u else 0 := by
  rw [← cert.transition, ← cert.transition, h]

theorem step_comp (f : W → ℝ) (v : V) :
    M.step (fun u => f (project u)) v = N.step f (project v) := by
  simp only [MarkovChain.step, cert.transition, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [ite_mul]

/-- No loss of the whole defeat-time CDF, not merely a one-step bound. -/
theorem h_eq (n : Nat) (v : V) : M.h n v = N.h n (project v) := by
  induction n generalizing v with
  | zero => simp only [h_zero, cert.defeat]
  | succ n ih =>
    simp only [h_succ, cert.defeat]
    split
    · rfl
    · change M.step (M.h n) v = N.step (N.h n) (project v)
      have hh : M.h n = fun u => N.h n (project u) := funext ih
      rw [hh]
      exact cert.step_comp _ _

theorem hInf_eq (v : V) : M.hInf v = N.hInf (project v) := by
  simp only [hInf, cert.h_eq]

theorem initial_h_eq (n : Nat) : M.h n M.initial = N.h n N.initial := by
  rw [cert.h_eq, cert.initial]

theorem fair_iff (v : V) (p q : ℝ) :
    M.IsMarkovpqFair v p q ↔ N.IsMarkovpqFair (project v) p q := by
  simp only [IsMarkovpqFair, cert.hInf_eq]

theorem twoStepBalanced_iff (v : V) (p q : ℝ) :
    M.IsMarkovTwoStepBalanced v p q ↔
      N.IsMarkovTwoStepBalanced (project v) p q := by
  simp only [IsMarkovTwoStepBalanced, cert.h_eq]

theorem stable_iff (v : V) (p₁ q₁ p₂ q₂ : ℝ) :
    M.IsMarkovStable v p₁ q₁ p₂ q₂ ↔
      N.IsMarkovStable (project v) p₁ q₁ p₂ q₂ := by
  simp only [IsMarkovStable, cert.fair_iff, cert.twoStepBalanced_iff]

theorem fairDistrib_iff (v : V)
    (D : MeasureTheory.ProbabilityMeasure (WithTop ℕ)) (ε : ℝ≥0) :
    M.IsMarkovFairDistrib v D ε ↔ N.IsMarkovFairDistrib (project v) D ε := by
  simp only [IsMarkovFairDistrib, cert.h_eq]

end ProjectionCertificate

end MarkovChain

/-- A directly checkable condition for an implemented one-step simulator with
explicit random input. Decisions must use the projected state as well. -/
def RespectsProjection {Full Reduced Roll : Type*} (project : Full → Reduced)
    (stepFull : Full → Roll → Full) (stepReduced : Reduced → Roll → Reduced) : Prop :=
  ∀ state roll, project (stepFull state roll) = stepReduced (project state) roll

/-- Reduction commutes with every finite sequence of supplied random outcomes.
Probability preservation additionally requires the same law of those outcomes;
the graph certificate above expresses this at the transition-matrix level. -/
theorem respectsProjection_run {Full Reduced Roll : Type*}
    {project : Full → Reduced} {stepFull : Full → Roll → Full}
    {stepReduced : Reduced → Roll → Reduced}
    (h : RespectsProjection project stepFull stepReduced)
    (state : Full) (rolls : List Roll) :
    project (rolls.foldl stepFull state) = rolls.foldl stepReduced (project state) := by
  induction rolls generalizing state with
  | nil => rfl
  | cons roll rolls ih =>
    simp only [List.foldl_cons, ih]
    rw [h state roll]

end MarkovRPG
