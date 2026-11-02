import Rpg.Play
import Rpg.Adventures.Lafayette.Confidence
import Rpg.WorldChange
import Rpg.EventGraph
import Rpg.Probability.FastBinomial

/-!
# The main theorems, as statements

This file is the trusted list of what the project proves, for `lake comparator`.
Each theorem here has the proof `sorry`. `Comparator/Proofs.lean` states the same theorems,
with the same names, and proves them. `lake comparator` checks that the two files state the
same thing, that the proofs pass the kernel, and that they use only the standard axioms.
Read this file, and the definitions it names, to know what the project proves.
-/

namespace Verified
open Rpg

/-- If the checker finds no errors, the Adventure is legal by the spec, under its rules. -/
theorem check_sound {rules : RuleSet} {c : Being} {a : Adventure}
    (h : check rules c a = []) : LegalAdventure rules c a := sorry

/-- If the Character checker finds no errors, the Character is a legal build, under the rules. -/
theorem checkCharacter_sound {rules : RuleSet} {c : Being}
    (h : checkCharacter rules c = []) : LegalCharacter rules c := sorry

/-- The built-in Adventure, Lafayette at Barren Hill, is legal for Lafayette under its rules. This
shows that the premise of `check_sound` can be met. -/
theorem barren_hill_legal : LegalAdventure Lafayette.rules Lafayette.lafayette Lafayette.barrenHill := sorry

/-- From every Scene of the built-in Adventure, an Ending can be reached. -/
theorem barren_hill_reaches_ending :
    ∀ s ∈ Lafayette.barrenHill.scenes, ReachesEnding Lafayette.barrenHill s.id := sorry

/-- An input that the game does not offer changes nothing and rolls no dice. -/
theorem step_rejects (g : Game) (i : Input) (dice : Rng)
    -- The game does not offer `i` now.
    (h : i ∉ g.inputs) :
    (step g i).run dice = ((g, [.rejected rejectedWhy]), dice) := sorry

/-- The game offers exactly the inputs that the rules allow. -/
theorem mem_inputs_iff {g : Game} {i : Input} : i ∈ g.inputs ↔ AllowedInput g i := sorry

/-- The built-in Adventure uses the default rules, in every place that play and the balance check
read them. A DM cannot change the rules without breaking this statement. -/
theorem barren_hill_default_rules :
    Lafayette.rules = {} ∧
    Lafayette.barrenHillDefinition.rules = {} ∧
    Lafayette.statisticalCandidate.rules = {} := sorry

/-- The built-in Adventure and generated Adventures both inherit the shared tactical meta rules. -/
theorem shared_tactical_rules :
    Lafayette.rules.combatRules = defaultCombatRules ∧
    liveRules.combatRules = defaultCombatRules := sorry

/-- The balance test is sound for every candidate, under the binomial sampling model. -/
theorem balanced (a : Probability.StatisticalCandidate) : Probability.Balanced a := sorry

/-- An in-play change cannot replace any of the core rules. -/
theorem live_change_core (p : WorldChange.Prepared) :
    p.game.rules.core = p.before.rules.core := sorry

/-- Changes preserve HP, completed choices, and the current scene. -/
theorem live_change_checkpoint (p : WorldChange.Prepared) :
    p.game.hp = p.before.hp ∧ p.game.trail = p.before.trail ∧
    p.game.sceneId? = p.before.sceneId? := sorry

/-- A live patch preserves each existing meta rule and earlier adventure effect. -/
theorem live_change_existing_rule (p : WorldChange.Prepared) (r : CombatRule)
    (existing : r ∈ p.before.rules.combatRules) : r ∈ p.game.rules.combatRules := sorry

/-- The simulated graph starts from the revised checkpoint, at the original elapsed event count. -/
theorem live_change_from_checkpoint (p : WorldChange.Prepared) :
    p.candidate.resume = some p.game.balancePoint ∧
    p.candidate.elapsed = p.before.trail.length ∧
    p.candidate.graph = Probability.continuationGraph p.definition p.game.balancePoint :=
  p.candidate_from_checkpoint

/-- The new start node keeps the current Scene and remaining HP. -/
theorem live_change_scene_start (p : WorldChange.Prepared) (id : SceneId)
    (scene : p.before.phase = .scene id) :
    p.candidate.resume = some (.scene id p.before.hp) ∧
    p.candidate.graph.start = Probability.arrive p.definition.story id p.before.hp :=
  p.candidate_scene_start id scene

/-- A paused Fight keeps HP, foes, maneuvers, round and order; only the granted build changes. -/
theorem live_change_fight_start (p : WorldChange.Prepared) (f : FightPhase)
    (fight : p.before.phase = .fight f) :
    p.before.hp = f.state.hero.hp ∧
    p.candidate.resume = some (.fight
      { f with state := { f.state with hero := { f.state.hero with being := p.definition.hero } } }) :=
  p.candidate_fight_start f fight

/-- Residual survival is the original Weibull curve conditioned on reaching this age. -/
theorem weibull_remaining_survival (policy : Probability.BalancePolicy)
    (valid : policy.Valid) (elapsed turns : Nat) :
    policy.remainingSurvival elapsed turns = policy.survival (elapsed + turns) / policy.survival elapsed :=
  policy.remainingSurvival_eq_ratio valid elapsed turns

/-- Targets refer to death anywhere in the next pair of events, at the original age. -/
theorem live_change_checkpoint_target (p : WorldChange.Prepared) (offset : Nat) :
    p.before.policy.checkpointTarget p.candidate.elapsed (offset+1) =
      1 - p.before.policy.survival (p.before.trail.length + offset + 2) /
        p.before.policy.survival (p.before.trail.length + offset) :=
  p.checkpoint_pair_target offset

/-- The actual tested probability is derived from this revised checkpoint graph. -/
theorem live_change_checkpoint_truth (p : WorldChange.Prepared) (offset : Nat)
    (within : offset + 1 < p.candidate.horizon + 1) :
    p.candidate.truth ⟨offset + 1, within⟩ =
      ((Probability.continuationGraph p.definition p.game.balancePoint).deathWithinTwo offset).getD 0 :=
  p.checkpoint_pair_truth offset within

/-- Every admitted confidence interval fits the aged target within five percentage points. -/
theorem live_change_checkpoint_intervals {p : WorldChange.Prepared} {seed : Nat} {delta : Rat}
    (a : WorldChange.Admission p seed delta) (i : Fin (p.candidate.horizon+1)) :
    let obs := a.counts.observation i.val
    let iv := Probability.Confidence.confidenceInterval delta obs.trials obs.deaths
    let target := p.before.policy.checkpointTarget p.before.trail.length i.val
    target - p.before.policy.tolerance ≤ iv.lower ∧ iv.upper ≤ target + p.before.policy.tolerance :=
  a.checkpoint_intervals i

/-- Covered accepted intervals imply the requested semantic property of the checkpoint graph. -/
theorem live_change_difficulty_if_covered {p : WorldChange.Prepared} {seed : Nat} {delta : Rat}
    (a : WorldChange.Admission p seed delta)
    (covered : ∀ i : Fin (p.candidate.horizon + 1),
      let obs := a.counts.observation i.val
      (Probability.Confidence.confidenceInterval delta obs.trials obs.deaths).Contains (p.candidate.truth i)) :
    p.CheckpointBalanced :=
  a.difficulty_preserved_if_covered covered

/-- The probability of falsely accepting the checkpoint graph is bounded under the sampling model. -/
theorem live_change_falseAcceptance (p : WorldChange.Prepared) (delta : Rat)
    (nonnegative : 0 ≤ delta)
    (law : Probability.Distribution (Fin (p.candidate.horizon + 1) → Probability.Confidence.Observation))
    (valid : law.Valid) (sampling : Probability.Confidence.BinomialSampling law p.candidate.truth)
    (probabilities : ∀ i, 0 ≤ p.candidate.truth i ∧ p.candidate.truth i ≤ 1) :
    Probability.Confidence.expectation law (fun observations =>
      if Probability.Confidence.acceptsFamily p.candidate.bands delta observations ∧ ¬ p.CheckpointBalanced
      then 1 else 0) ≤ delta :=
  p.checkpoint_falseAcceptance delta nonnegative law valid sampling probabilities

-- The fact about one admission is `WorldChange.Admission.intervals_fit`.
/-- The balance test at error allowance `delta` is sound for the changed Adventure, from its
start. This holds for every proposal: it limits how often the test accepts an unbalanced change. It
does not say that this change is balanced. -/
theorem live_change_balanced {p : WorldChange.Prepared} {seed : Nat} {delta : Rat}
    (a : WorldChange.Admission p seed delta) :
    Probability.BalancedAt p.candidate delta p.candidate.policy := sorry

/-- Any finite adaptive series of live-change validations stays within the shared risk budget. -/
theorem retry_balanced {n : Nat} (tree : Probability.RetryTree n)
    (valid : tree.Valid) : tree.falseAcceptance 0 ≤ Probability.Confidence.confidenceDelta := sorry

/-- A live change keeps the balance policy of the Adventure, and its check uses that policy. -/
theorem live_change_policy (p : WorldChange.Prepared) :
    -- The changed game has the policy of the game before the change.
    p.game.policy = p.before.policy ∧
    -- The balance check of the change uses that policy.
    p.candidate.policy = p.before.policy := sorry

/-- The default balance curve: Weibull with q = 19/20 and shape 2, and a tolerance of 20 points. It
has valid parameters. Every Adventure uses it. -/
theorem default_policy :
    -- The curve has valid Weibull parameters and a tolerance that is not vacuous.
    Probability.defaultPolicy.Valid ∧
    -- The Weibull retention q is 19/20.
    Probability.defaultPolicy.retention = 19 / 20 ∧
    -- The Weibull shape is 2.
    Probability.defaultPolicy.shape = 2 ∧
    -- The tolerance is 20 points.
    Probability.defaultPolicy.tolerance = 1 / 5 := sorry

/-- A Game from a Draft uses the default balance curve. After the balance check, the check
admitted the Draft as a candidate with the default curve. On the fast load of an admitted Draft,
no check runs, and the Game has the default curve. -/
theorem draft_game_policy (d : Draft) (seed : Nat) (g : Game) :
    -- A Game that passed the balance check comes from a check with the default curve.
    (d.toGame seed = .ok g →
      ∃ (defn : AdventureDefinition) (counts : Probability.ValidationCounts)
        (a : Probability.StatisticalAdventure),
        Probability.admitWithSeed (liveCandidate defn) seed = (counts, some a) ∧
        a.candidate.policy = Probability.defaultPolicy ∧
        g = Game.new a.candidate.toAdventureDefinition Probability.defaultPolicy) ∧
    -- A Game from the fast load has the default curve.
    (d.toGameAdmitted = .ok g → g.policy = Probability.defaultPolicy) := sorry

/-- If the short-loop check passes, every loop has at least 4 steps: a path of Choices from a
Scene back to the same Scene, with at least one step, has 4 steps or more. -/
theorem noShortLoops (a : Adventure) {s : SceneId} {n : Nat}
    -- The short-loop check passes.
    (checked : a.checkShortLoops = true)
    -- Following `n` Choices leads from `s` back to `s`.
    (loop : ChoicePath a s s n)
    -- The path has at least one step.
    (positive : 0 < n) :
    4 ≤ n := sorry

/-- The fast binomial expectation that the compiled balance check runs is equal to
`exactExpectation`, the function that the balance proofs are about. -/
theorem exactExpectation_eq_fast :
    @Probability.Confidence.exactExpectation = @Probability.Confidence.Fast.fastExactExpectation := sorry

/-- One timestamped target formula applies to both initial and revised adventures. -/
theorem timestamped_balance_target (d : AdventureDefinition) (point : Probability.ResumePoint)
    (elapsed horizon : Nat) (positive : 0 < horizon) (policy : Probability.BalancePolicy)
    (valid : policy.Valid) (offset : Nat) (within : offset + 1 < horizon + 1) :
    ((Probability.StatisticalCandidate.atCheckpoint d point elapsed horizon positive policy).bands
      ⟨offset + 1, within⟩).target =
      1 - policy.survival (elapsed + offset + 2) / policy.survival (elapsed + offset) :=
  Probability.StatisticalCandidate.timestamp_target d point elapsed horizon positive policy valid offset within

/-- Accepted covered intervals imply the common meta property, for every adventure and checkpoint. -/
theorem timestamped_balance_if_covered (a : Probability.StatisticalCandidate)
    (counts : Probability.ValidationCounts) (delta : Rat) (accepted : a.accepts counts delta)
    (covered : ∀ i : Fin (a.horizon + 1),
      let obs := counts.observation i.val
      let iv := Probability.Confidence.confidenceInterval delta obs.trials obs.deaths
      iv.lower ≤ a.truth i ∧ a.truth i ≤ iv.upper) : a.FitsBands :=
  a.fits_if_covered counts delta accepted covered

/-- Every live graph edit rebuilds the exact logical projection used by the 3D renderer. -/
theorem live_change_spatial_matches (p : WorldChange.Prepared) :
    (∀ source target, (source, target) ∈ p.game.spatialProjection.links ↔ Leads p.game.adventure source target) ∧
    (∀ input, input ∈ p.game.spatialProjection.inputs ↔ AllowedInput p.game input) := p.spatial_matches

end Verified
