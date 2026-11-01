import Rpg.Play
import Rpg.Adventures.Lighthouse.Confidence
import Rpg.WorldChange

/-!
# The main theorems, with proofs

This file proves the statements in `Comparator/Statements.lean`, with the same names.
-/

namespace Verified
open Rpg

/-- If the checker finds no errors, the Adventure is legal by the spec, under its rules. -/
theorem check_sound {rules : RuleSet} {c : Being} {a : Adventure}
    (h : check rules c a = []) : LegalAdventure rules c a := Rpg.check_sound h

/-- If the Character checker finds no errors, the Character is a legal build, under the rules. -/
theorem checkCharacter_sound {rules : RuleSet} {c : Being}
    (h : checkCharacter rules c = []) : LegalCharacter rules c := Rpg.checkCharacter_sound h

/-- The Drowned Lighthouse is legal for Mara under its rules. -/
theorem lighthouse_legal : LegalAdventure Lighthouse.rules Lighthouse.mara Lighthouse.lighthouse :=
  Lighthouse.lighthouse_legal

/-- From every Scene of The Drowned Lighthouse, an Ending can be reached. -/
theorem lighthouse_reaches_ending :
    ∀ s ∈ Lighthouse.lighthouse.scenes, ReachesEnding Lighthouse.lighthouse s.id :=
  Lighthouse.lighthouse_reaches_ending

/-- An input that the game does not offer changes nothing and rolls no dice. -/
theorem step_rejects (g : Game) (i : Input) (dice : Rng)
    -- The game does not offer `i` now.
    (h : i ∉ g.inputs) :
    (step g i).run dice = ((g, [.rejected rejectedWhy]), dice) := Rpg.step_rejects g i dice h

/-- The game offers exactly the inputs that the rules allow. -/
theorem mem_inputs_iff {g : Game} {i : Input} : i ∈ g.inputs ↔ AllowedInput g i := Rpg.mem_inputs_iff

/-- The Lighthouse uses the default rules, in every place that play and the balance check read
them. A DM cannot change the rules without breaking this statement. -/
theorem lighthouse_default_rules :
    Lighthouse.rules = {} ∧
    Lighthouse.lighthouseDefinition.rules = {} ∧
    Lighthouse.statisticalCandidate.rules = {} :=
  ⟨rfl, rfl, rfl⟩

/-- The balance test is sound for every candidate, under the binomial sampling model. -/
theorem balanced (a : Probability.StatisticalCandidate) : Probability.Balanced a := a.balanced

/-- An in-play change cannot replace any of the core rules. -/
theorem live_change_core (p : WorldChange.Prepared) :
    p.game.rules.core = p.before.rules.core := p.preserves_core

/-- Changes preserve HP, completed choices, and the current scene. -/
theorem live_change_checkpoint (p : WorldChange.Prepared) :
    p.game.hp = p.before.hp ∧ p.game.trail = p.before.trail ∧
    p.game.sceneId? = p.before.sceneId? := p.preserves_checkpoint

/-- Checking starts at the updated adventure's beginning; play retains its checkpoint. -/
theorem live_change_from_start (p : WorldChange.Prepared) :
    p.candidate.resume = none ∧ p.candidate.elapsed = 0 ∧
    p.candidate.graph = p.definition.graph := p.candidate_from_start

-- The fact about one admission is `WorldChange.Admission.intervals_fit`.
/-- The balance test at error allowance `delta` is sound for the changed Adventure, from its
start. This holds for every proposal: it limits how often the test accepts an unbalanced change. It
does not say that this change is balanced. -/
theorem live_change_balanced {p : WorldChange.Prepared} {seed : Nat} {delta : Rat}
    (a : WorldChange.Admission p seed delta) : Probability.BalancedAt p.candidate delta := a.balanced

/-- Any finite adaptive series of live-change validations stays within the shared risk budget. -/
theorem retry_balanced {n : Nat} (tree : Probability.RetryTree n)
    (valid : tree.Valid) : tree.falseAcceptance 0 ≤ Probability.Confidence.confidenceDelta :=
  tree.balanced 0 valid

end Verified
