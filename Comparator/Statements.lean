import Rpg.Play
import Rpg.GraphValidity
import Rpg.Adventures.Lighthouse.Confidence

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

/-- The fairness test is sound for every candidate, under the binomial sampling model. -/
theorem fair (a : Probability.StatisticalCandidate) : Probability.Fair a := sorry

/-- The graph validity certificate includes legality, event structure and observed balance. -/
theorem balanced (g : ValidatedGraph) :
    GraphValid g.statistical.candidate g.statistical.seed g.statistical.counts :=
  g.balanced

/-- Every nonempty closed event walk of a checked graph has at least four edges. -/
theorem noSmallCycles (a : Adventure)
    (checked : a.checkEventCycles = true)
    (walk : EventWalk a s s n)
    (positive : 0 < n) : 4 ≤ n :=
  a.noSmallCycles checked walk positive

end Verified
