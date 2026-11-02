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
  graphStable := by decide +kernel
  noShortLoops := by decide +kernel
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

-- Execute the precommitted-batch regression through the proved admission gate.
-- The general theorem is kernel checked; enumerating thousands of deterministic simulations
-- in the proof kernel adds no probability guarantee and is unnecessarily expensive.
#guard (gentlePrepared.admit validationSeed (attemptRisk 0)).2.isSome

-- A concrete graph satisfies the shared semantic property, without assumed premises.
example : gentlePrepared.CheckpointBalanced := by decide +kernel

-- A safe world is too safe for main's unchanged default curve.
#guard match ironSkin.prepare { gentleGame with policy := defaultPolicy } with
  | .error _ => false
  | .ok p => (p.admit validationSeed (attemptRisk 0)).2.isNone

-- The checkpoint age matters even though the world and HP are unchanged.
#guard
  let c := sampleCounts gentlePrepared.candidate validationSeed validationGames
  decide (ValidationAccepted liveHorizon c (attemptRisk 0) 0 gentleGame.policy .window) &&
    !decide (ValidationAccepted liveHorizon c (attemptRisk 0) 30 gentleGame.policy .window)

-- A point estimate in the band still fails if its interval protrudes beyond the band.
example : WithinTolerance (20/100) (20/100) (1/20) ∧
    ¬ acceptsCount ⟨20/100, 1/20⟩ confidenceDelta ⟨10, 2⟩ := by decide +kernel

/-- Precision planning uses the absolute timestamp but samples only the new six-event window. -/
def referenceCounts (a : StatisticalCandidate) : ValidationCounts := Id.run do
  let mut c : ValidationCounts := ⟨#[], #[], a.games, false, false⟩
  for row in [:a.horizon+1] do
    let n := if row == 0 then a.games else
      ((a.games : Rat) * a.policy.remainingSurvival a.elapsed (row-1)).floor.toNat
    let k := ((n : Rat) * a.policy.checkpointTarget a.elapsed row + 1/2).floor.toNat
    c := { c with trials := c.trials.push n, deaths := c.deaths.push k }
  return c

-- Reference-centered counts can pass at initial and late timestamps under main's policy.
#guard [0, 5, 10].all fun age =>
  let a := { gentlePrepared.candidate with elapsed := age, policy := defaultPolicy }
  decide (a.accepts (referenceCounts a) (attemptRisk 0))

-- Initial admission keeps main's point-probability rule and timestamp zero.
example : (liveCandidate gentlePrepared.definition).protocol = .point ∧
    (liveCandidate gentlePrepared.definition).elapsed = 0 ∧
    (liveCandidate gentlePrepared.definition).policy = defaultPolicy := ⟨rfl, rfl, rfl⟩

example : (StatisticalCandidate.atCheckpoint gentlePrepared.definition
    (.scene 0 2) 10 5 (by decide) defaultPolicy).elapsed = 10 := rfl

/-- Add a current-scene option and a new event with its spatial placement. -/
def addEvent : Proposal :=
  { summary := "Add a lookout", moment := "A path opens.", equipment := none, rules := [],
    scenes := [
      { id := 0, title := "The Storm", text := "Two routes lead to shelter."
        choices := [{ text := "Take shelter", outcome := .goto 1 },
          { text := "Visit the lookout", outcome := .goto 2 }] },
      { id := 2, title := "The lookout", text := "Shelter is nearby."
        choices := [{ text := "Take shelter", outcome := .goto 1 }] }],
    scenePlaces := [{ scene := 2, place := 1 }] }

-- The same event edit is refused during a fight, before statistical admission.
#guard match addEvent.prepare fightGame with
  | .error errors => errors.contains
      "The event graph cannot change during a fight. Finish the fight before editing scenes or choices."
  | .ok _ => false

-- This checks real graph patches and generated render data, not a parallel test graph.
#guard match addEvent.prepare gentleGame (some (mapFor gentleGame)) with
  | .error _ => false
  | .ok p =>
    let rendered := p.game.spatialProjection
    let remove : Proposal := { addEvent with
      scenes := [{ id := 0, title := "The Storm", text := "One route remains.", choices := [{ text := "Visit the lookout", outcome := .goto 2 }] }], scenePlaces := [] }
    match remove.prepare p.game (addEvent.environmentAfter (some (mapFor gentleGame))) with
    | .error _ => false
    | .ok q =>
      (p.admit validationSeed (attemptRisk 0)).2.isSome &&
      (q.admit validationSeed (attemptRisk 0)).2.isSome &&
      rendered.scenes.contains 2 && rendered.links.contains (0, 2) &&
      rendered.inputs.length == 2 && q.game.spatialProjection.inputs.length == 1 &&
      !q.game.spatialProjection.links.contains (0, 1) &&
      q.game.hp == gentleGame.hp && q.candidate.elapsed == gentleGame.trail.length

/-- A meeting is an event and an offered choice, with its NPC placed in the world. -/
def meetNapoleon : Proposal :=
  { addEvent with
    summary := "Napoleon offers advice.", moment := "A route to his camp opens."
    scenes := [
      { id := 0, title := "The Storm", text := "A messenger points toward the camp."
        choices := [{ text := "Take shelter", outcome := .goto 1 },
          { text := "Meet Napoleon for advice", outcome := .goto 2 }] },
      { id := 2, title := "Napoleon's advice", text := "Napoleon says: Scout the route and protect your supplies before advancing."
        choices := [{ text := "Thank Napoleon and continue", outcome := .goto 1 }] }],
    scenePlaces := [{ scene := 2, place := 1, npcs := ["Napoleon"] }] }

-- Execute the actual command to reach the added meeting; no cosmetic-only shortcut can install it.
#guard match meetNapoleon.prepare gentleGame (some (mapFor gentleGame)) with
  | .error _ => false
  | .ok p =>
    let (met, _) := (step p.game (.choose 1)).run' ⟨7⟩
    !decide p.proposal.visualOnly &&
      (p.admit validationSeed (attemptRisk 0)).2.isSome &&
      met.sceneId? == some 2 && met.trail.length == gentleGame.trail.length + 1 &&
      met.spatialProjection.scenes.contains 2 &&
      (meetNapoleon.environmentAfter (some (mapFor gentleGame))).any
        (fun e => e.scenes.any (fun s => s.scene == 2 && s.npcs.contains "Napoleon"))

-- A permissive exploratory screen can never authorize a batch by itself.
#guard
  let a := { gentlePrepared.candidate with policy := defaultPolicy }
  let sparse : ValidationCounts := ⟨Array.replicate 6 0, Array.replicate 6 0, screenGames, false, false⟩
  a.screenPlausible sparse && !decide (a.accepts sparse (attemptRisk 0))

-- The render projection rejects invented commands and event links.
example : (.choose 1) ∈ roadGame.spatialProjection.inputs := by decide +kernel
example : (.choose 999) ∉ roadGame.spatialProjection.inputs := by decide +kernel
example : (0, 1) ∈ roadGame.spatialProjection.links := by decide +kernel
example : (0, 999) ∉ roadGame.spatialProjection.links := by decide +kernel

end Rpg.WorldChange.Tests
