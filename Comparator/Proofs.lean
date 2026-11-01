import Rpg.Play
import Rpg.GraphValidity
import Rpg.Adventures.Lighthouse.Confidence

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

/-- The Lighthouse uses the default rules, in every place that play and the fairness check read
them. A DM cannot change the rules without breaking this statement. -/
theorem lighthouse_default_rules :
    Lighthouse.rules = {} ∧
    Lighthouse.lighthouseDefinition.rules = {} ∧
    Lighthouse.statisticalCandidate.rules = {} :=
  ⟨rfl, rfl, rfl⟩

/-- The fairness test is sound for every candidate, under the binomial sampling model. -/
theorem fair (a : Probability.StatisticalCandidate) : Probability.Fair a := a.fair

/-- The graph validity certificate includes legality, event structure and observed balance. -/
theorem equilibrium (g : ValidatedGraph) :
    GraphValid g.statistical.candidate g.statistical.seed g.statistical.counts :=
  g.equilibrium

/-- Every nonempty closed event walk of a checked graph has at least four edges. -/
theorem «non-cyclic» (a : Adventure)
    (checked : a.checkEventCycles = true)
    (walk : EventWalk a s s n)
    (positive : 0 < n) : 4 ≤ n :=
  a.«non-cyclic» checked walk positive

end Verified
