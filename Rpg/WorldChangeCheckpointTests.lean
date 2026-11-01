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
  pure (fun _ => ⟨gentlePrepared.candidate.games, 0⟩)

theorem gentleLaw_valid : gentleLaw.Valid := by
  simp [gentleLaw, Distribution.Valid, pure, Pure.pure]
  decide +kernel

def gentleLaw_sampling : BinomialSampling gentleLaw gentlePrepared.candidate.truth where
  sizes := fun _ => pure gentlePrepared.candidate.games
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

-- Execute the full 5,000-run regression through the proved admission gate.
-- The general theorem is kernel checked; enumerating thousands of deterministic simulations
-- in the proof kernel adds no probability guarantee and is unnecessarily expensive.
#guard (gentlePrepared.admit validationSeed (attemptRisk 0)).2.isSome

-- A concrete graph satisfies the shared semantic property, without assumed premises.
example : gentlePrepared.CheckpointBalanced := by decide +kernel

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

/-- Precision planning uses the absolute timestamp but samples only the new six-event window. -/
def referenceCounts (a : StatisticalCandidate) : ValidationCounts := Id.run do
  let mut c : ValidationCounts := ⟨#[], #[], a.games, false⟩
  for row in [:a.horizon+1] do
    let n := if row == 0 then a.games else
      ((a.games : Rat) * a.policy.remainingSurvival a.elapsed (row-1)).floor.toNat
    let k := ((n : Rat) * a.policy.checkpointTarget a.elapsed row + 1/2).floor.toNat
    c := { c with trials := c.trials.push n, deaths := c.deaths.push k }
  return c

-- The former 1,200-run plan could not admit even ideal counts at hard, age 10.
-- The new precommitted plan supports every selectable level at both timestamps.
#guard [0, 10].all fun age => DifficultyLevel.all.all fun level =>
  let a := { gentlePrepared.candidate with elapsed := age, policy := level.policy }
  decide (a.accepts (referenceCounts a) (attemptRisk 0))

-- Initial and live admission share the same constructor, policy, targets and six-event window.
example : liveCandidate gentlePrepared.definition gentleGame.policy =
    StatisticalCandidate.atCheckpoint gentlePrepared.definition
      (.scene gentlePrepared.definition.story.start
        (gentlePrepared.definition.rules.maxHP gentlePrepared.definition.hero))
      0 5 (by decide) gentleGame.policy := rfl

example : (StatisticalCandidate.atCheckpoint gentlePrepared.definition
    (.scene 0 2) 10 5 (by decide) DifficultyLevel.hard.policy).elapsed = 10 := rfl

end Rpg.WorldChange.Tests
