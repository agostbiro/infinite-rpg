import Rpg.Play
import Rpg.Adventures.Lighthouse.Confidence
import Rpg.WorldChange

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

/-- The Drowned Lighthouse is legal for Mara under its rules. -/
theorem lighthouse_legal : LegalAdventure Lighthouse.rules Lighthouse.mara Lighthouse.lighthouse := sorry

/-- From every Scene of The Drowned Lighthouse, an Ending can be reached. -/
theorem lighthouse_reaches_ending :
    ∀ s ∈ Lighthouse.lighthouse.scenes, ReachesEnding Lighthouse.lighthouse s.id := sorry

/-- An input that the game does not offer changes nothing and rolls no dice. -/
theorem step_rejects (g : Game) (i : Input) (dice : Rng)
    -- The game does not offer `i` now.
    (h : i ∉ g.inputs) :
    (step g i).run dice = ((g, [.rejected rejectedWhy]), dice) := sorry

/-- The game offers exactly the inputs that the rules allow. -/
theorem mem_inputs_iff {g : Game} {i : Input} : i ∈ g.inputs ↔ AllowedInput g i := sorry

/-- The Lighthouse uses the default rules, in every place that play and the fairness check read
them. A DM cannot change the rules without breaking this statement. -/
theorem lighthouse_default_rules :
    Lighthouse.rules = {} ∧
    Lighthouse.lighthouseDefinition.rules = {} ∧
    Lighthouse.statisticalCandidate.rules = {} := sorry

/-- Built-in and generated adventures both inherit the shared tactical meta rules. -/
theorem shared_tactical_rules :
    Lighthouse.rules.combatRules = defaultCombatRules ∧
    liveRules.combatRules = defaultCombatRules := sorry

/-- The fairness test is sound for every candidate, under the binomial sampling model. -/
theorem fair (a : Probability.StatisticalCandidate) : Probability.Fair a := sorry

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

/-- Checking starts at the updated adventure's beginning; play retains its checkpoint. -/
theorem live_change_from_start (p : WorldChange.Prepared) :
    p.candidate.resume = none ∧ p.candidate.elapsed = 0 ∧
    p.candidate.graph = p.definition.graph := sorry

/-- Admission supplies fairness for the updated adventure from its beginning. -/
theorem live_change_fair {p : WorldChange.Prepared} {seed : Nat} {delta : Rat}
    (a : WorldChange.Admission p seed delta) : Probability.FairAt p.candidate delta := sorry

/-- Any finite adaptive series of live-change validations stays within the shared risk budget. -/
theorem retry_fair {n : Nat} (tree : Probability.RetryTree n)
    (valid : tree.Valid) : tree.falseAcceptance 0 ≤ Probability.Confidence.confidenceDelta := sorry

end Verified
