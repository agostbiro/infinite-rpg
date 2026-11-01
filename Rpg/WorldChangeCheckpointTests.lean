import Rpg.WorldChangeTests

/-! Concrete positive and negative instances of checkpoint admission.
The gentle curve is a test fixture, not a new selectable difficulty level. -/
namespace Rpg.WorldChange.Tests
open Probability Probability.Confidence

/-- A known safe world with a valid reference whose six-event band includes zero risk. -/
def gentleGame : Game :=
  { Game.new TestStory.safeDefinition with
    phase := .scene 0
    policy := ⟨999/1000, 2, 1/20⟩ }

/-- Preparation succeeds with real rules and legality proofs, not assumed premises. -/
def gentlePrepared : Prepared where
  before := gentleGame
  proposal := ironSkin
  proposalValid := by decide +kernel
  policyValid := by decide +kernel
  checkpointValid := by decide +kernel
  heroLegal := checkCharacter_sound (by decide +kernel)
  storyLegal := check_sound (by decide +kernel)

#guard (ironSkin.prepare gentleGame).toOption.isSome

example : gentlePrepared.candidate.resume = some (.scene 0 gentleGame.hp) ∧
    gentlePrepared.candidate.graph.start = arrive gentlePrepared.definition.story 0 gentleGame.hp :=
  gentlePrepared.candidate_scene_start 0 rfl

example : gentleGame.policy.remainingSurvival 3 2 =
    gentleGame.policy.survival 5 / gentleGame.policy.survival 3 :=
  gentleGame.policy.remainingSurvival_eq_ratio (by decide +kernel) 3 2

/-- This actual revised graph has no lethal edges. -/
theorem gentle_truth_zero : ∀ i, gentlePrepared.candidate.truth i = 0 := by decide +kernel

/-- The fixed batch has a deterministic law in this safe world. -/
def gentleLaw : Distribution (Fin (gentlePrepared.candidate.horizon+1) → Observation) :=
  pure (fun _ => ⟨difficultyGames, 0⟩)

theorem gentleLaw_valid : gentleLaw.Valid := by
  simp [gentleLaw, Distribution.Valid, pure, Pure.pure]
  decide +kernel

def gentleLaw_sampling : BinomialSampling gentleLaw gentlePrepared.candidate.truth where
  sizes := fun _ => pure difficultyGames
  sizesValid := by
    intro i
    simp [Distribution.Valid, pure, Pure.pure]
    decide +kernel
  marginals := by
    intro i f
    rw [gentle_truth_zero]
    simp [gentleLaw, expectation, pure, Pure.pure, zero_sampling]

-- All assumptions of the checkpoint risk theorem can be discharged on executable game data.
example : expectation gentleLaw (fun observations =>
    if acceptsFamily gentlePrepared.candidate.bands (attemptRisk 0) observations ∧
      ¬ gentlePrepared.CheckpointBalanced then 1 else 0) ≤ attemptRisk 0 := by
  apply gentlePrepared.checkpoint_falseAcceptance (attemptRisk 0) (by decide +kernel)
    gentleLaw gentleLaw_valid gentleLaw_sampling
  intro i
  rw [gentle_truth_zero]
  decide +kernel

-- Kernel reduction of the complete 1,200-game fixture needs more recursion than small examples.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- A full source-bound admission exists: real simulations, all six rows, and a held-out seed. -/
theorem gentle_admitted : (gentlePrepared.admit validationSeed (attemptRisk 0)).2.isSome = true :=
  by decide +kernel

/-- An actual admission certificate with all its hypotheses discharged. -/
def gentleAdmission : Admission gentlePrepared validationSeed (attemptRisk 0) :=
  (gentlePrepared.admit validationSeed (attemptRisk 0)).2.get gentle_admitted

-- The semantic theorem also applies to an admitted world with known true probabilities.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
example : gentlePrepared.CheckpointBalanced :=
  gentleAdmission.difficulty_preserved_if_covered (by decide +kernel)

-- The same safe world is too safe for every selectable difficulty over this window.
#guard DifficultyLevel.all.all fun level =>
  match ironSkin.prepare { gentleGame with policy := level.policy } with
  | .error _ => false
  | .ok p => (p.admit validationSeed (attemptRisk 0)).2.isNone

-- The checkpoint age matters even though the world and HP are unchanged.
#guard
  let c := sampleCounts gentlePrepared.candidate validationSeed difficultyGames
  decide (ValidationAccepted liveHorizon c (attemptRisk 0) 0 gentleGame.policy .window) &&
    !decide (ValidationAccepted liveHorizon c (attemptRisk 0) 30 gentleGame.policy .window)

-- A point estimate in the band still fails if its interval protrudes beyond the band.
example : WithinTolerance (20/100) (20/100) (1/20) ∧
    ¬ acceptsCount ⟨20/100, 1/20⟩ confidenceDelta ⟨10, 2⟩ := by decide +kernel

end Rpg.WorldChange.Tests
