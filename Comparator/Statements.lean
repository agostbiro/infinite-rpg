import Rpg.Probability.DiceRefinement
import Rpg.Play
import Rpg.HPInvariant
import Rpg.Probability.GraphProofs
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

/-- Checking starts at the updated adventure's beginning; play retains its checkpoint. -/
theorem live_change_from_start (p : WorldChange.Prepared) :
    p.candidate.resume = none ∧ p.candidate.elapsed = 0 ∧
    p.candidate.graph = p.definition.graph := sorry

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

/-- A certified fight ends with probability one under independent fair dice and the uniform policy. -/
theorem combat_almostSurely {rules : RuleSet} {order : List Actor} {s : FightState}
    (c : Probability.CertifiedFight rules order s) :
    (Probability.combatProcess rules order).AlmostSurelyTerminates s := sorry

/-- A certified fight supplies a finite horizon for every positive failure allowance. -/
theorem combat_highProbability {rules : RuleSet} {order : List Actor} {s : FightState}
    (c : Probability.CertifiedFight rules order s) (delta : Rat) (positive : 0 < delta) :
    (Probability.combatProcess rules order).unfinished (c.stopping.horizon s delta) s ≤ delta := sorry

/-- Certified result probabilities agree with finite shared-engine executions to any requested error. -/
theorem combat_outcome_error {rules : RuleSet} {order : List Actor} {s : FightState}
    (c : Probability.CertifiedFight rules order s) (event : Probability.CombatResult → Bool)
    (delta : Rat) (positive : 0 < delta) :
    let exact := (Probability.combatProcess rules order).eventBy
      (fun s => event (Probability.terminalResult s)) (c.stopping.horizon s delta) s
    exact ≤ c.outcomes.mass event ∧ c.outcomes.mass event ≤ exact + delta := sorry

/-- Every admitted encounter terminates almost surely at every possible entry HP. -/
theorem admitted_combats (a : Probability.StatisticalAdventure) (foes : List Being)
    (encounter : foes ∈ Probability.encounterFoes a.candidate.story)
    (hp : Int) (lower : 0 ≤ hp) (upper : hp ≤ a.candidate.rules.maxHP a.candidate.hero) :
    (Probability.combatProcess a.candidate.rules (turnOrder a.candidate.rules a.candidate.hero foes)).AlmostSurelyTerminates
      (Probability.fightStart a.candidate.rules a.candidate.hero hp foes) := sorry

/-- A new game is well formed and its Character starts alive. -/
theorem runtime_initialized (d : AdventureDefinition) (policy : Probability.BalancePolicy) :
    (Game.new d policy).WellFormed ∧ 0 < (Game.new d policy).hp := sorry

/-- Every input, including rejected inputs, preserves runtime consistency. -/
theorem runtime_preserved (g : Game) (i : Input) (rng : Rng) (valid : g.WellFormed) :
    ((step g i).run' rng).1.WellFormed := sorry

/-- Every well-formed nonterminal game offers a rule-allowed input. -/
theorem runtime_progress (g : Game) (valid : g.WellFormed) (ongoing : ¬ g.Terminal) :
    ∃ i, AllowedInput g i := sorry

/-- Normal gameplay never increases HP, so entry-HP certification has a finite bound. -/
theorem hp_nonincreasing (g : Game) (i : Input) (rng : Rng) (valid : g.WellFormed) :
    ((step g i).run' rng).1.hp ≤ g.hp := sorry

/-- The generated graph has normalized kernels and absorbing terminal states. -/
theorem generated_graph_valid (rules : RuleSet) (hero : Being) (story : Adventure) :
    (Probability.adventureGraph rules hero story).Valid ∧
    (Probability.adventureGraph rules hero story).Absorbing := sorry

/-- An admitted live change preserves a valid runtime checkpoint. -/
theorem live_change_runtime {p : WorldChange.Prepared} {seed : Nat} {delta : Rat}
    (a : WorldChange.Admission p seed delta) : p.game.WellFormed := sorry

/-- Every admitted adventure retains the short-loop guarantee. -/
theorem admitted_noShortLoops (a : Probability.StatisticalAdventure) {s : SceneId} {n : Nat}
    (loop : ChoicePath a.candidate.story s s n) (positive : 0 < n) : 4 ≤ n := sorry

/-- The exact round model agrees with full independent fair-d6 execution of the shared engine. -/
theorem combat_full_dice (rules : RuleSet)
    (policy : FightState → Probability.Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (Probability.roundDistribution rules policy order s).expect observe =
      (roundWith (Probability.fullDiceAttack rules) policy order s).expect
        (fun result => observe result.1) := sorry

end Verified
