import Rpg.Probability.Fairness

/-! Small positive and negative fixtures check the probability specification. -/
namespace Rpg.Probability

/-- Rules owned by the probability test fixtures, not borrowed from a story. -/
def fixtureRules : RuleSet := {}

/-- A simple graph that ends safely after one turn. -/
def safeGraph : Graph where
  start := .scene 0 1
  step node := match node with
    | .dead => pure .dead
    | .stalled => pure .stalled
    | _ => pure .ended

/-- Safe play has finished after any positive number of turns. -/
theorem safeGraph_after (n : Nat) : safeGraph.after (n + 1) = pure Node.ended := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [Graph.after, ih]
    decide +kernel

/-- The policy admits a concrete graph with an actual initial choice. -/
theorem safeGraph_isFair : isFair defaultPolicy safeGraph := by
  refine ⟨defaultPolicy_valid, ?_, by decide +kernel, by decide +kernel, ?_⟩
  · constructor
    · intro node
      cases node <;> simp [safeGraph, Distribution.Valid, pure, Pure.pure] <;> decide +kernel
    · exact ⟨rfl, rfl, rfl⟩
  · intro t actual observed
    cases t with
    | zero =>
      have h : safeGraph.deathAtTwo 0 = some 0 := by decide +kernel
      rw [h] at observed
      cases observed
      decide +kernel
    | succ n =>
      have inactive : safeGraph.activeAt (n + 1) = 0 := by
        rw [Graph.activeAt, safeGraph_after]
        decide +kernel
      simp [Graph.deathAtTwo, inactive] at observed

/-- A lethal graph kills with certainty on turn two. -/
def lethalGraph : Graph where
  start := .scene 0 1
  step node := match node with
    | .scene 0 _ => pure (.scene 1 1)
    | .scene _ _ => pure .dead
    | .dead => pure .dead
    | .ended => pure .ended
    | .stalled => pure .stalled

/-- Exact two-turn death is certain in the bad graph. -/
theorem lethalGraph_death : lethalGraph.deathAtTwo 0 = some 1 := by decide +kernel

/-- The default policy rejects a concrete lethal graph. -/
theorem lethalGraph_not_fair : ¬ isFair defaultPolicy lethalGraph := by
  apply not_isFair_of_violation lethalGraph_death
  decide +kernel

/-- Tightening the default tolerance to zero invalidates the safe example's certificate. -/
theorem safeGraph_not_fair_zero_tolerance :
    ¬ isFair { defaultPolicy with tolerance := 0 } safeGraph := by
  apply not_isFair_of_violation (g := safeGraph) (t := 0) (actual := 0)
  · decide +kernel
  · decide +kernel

/-- A certain death on turn one is rejected by the first-turn guard. -/
def instantDeathGraph : Graph where
  start := .scene 0 1
  step node := match node with
    | .ended => pure .ended
    | .stalled => pure .stalled
    | _ => pure .dead

/-- Testing only death at t+2 would miss this unfair graph. -/
theorem instantDeathGraph_not_fair : ¬ isFair defaultPolicy instantDeathGraph := by
  intro fair
  have invalid : ¬ WithinTolerance (instantDeathGraph.deadBy 1)
      (1 - defaultPolicy.survival 1) defaultPolicy.tolerance := by decide +kernel
  exact invalid fair.2.2.2.1

/-- The safe example has expected termination time one at every positive horizon. -/
example : safeGraph.terminationPartial 4 = 1 := by decide +kernel

/-- Surviving a successful ending is not mistaken for dying. -/
example : safeGraph.deathPartial 4 = 4 := by decide +kernel

/-- Death-conditional time is undefined when there are no deaths. -/
example : safeGraph.conditionalDeathPartial 4 = none := by decide +kernel

/-- The lethal example terminates on turn two. -/
example : lethalGraph.terminationPartial 4 = 2 := by decide +kernel

/-- Conditioning on certain death yields the correct time. -/
example : lethalGraph.conditionalDeathPartial 4 = some 2 := by decide +kernel

/-- A roll against DX 10 succeeds on exactly half of 3d6 outcomes. -/
def rollHero : Being := ⟨"Roll fixture", 10, 10, 10, 10, [], .punch, .none, 0⟩

example : rollProbability fixtureRules rollHero (.attribute .dx) 0 = 1 / 2 := by decide +kernel
example : rollProbability fixtureRules rollHero (.attribute .dx) (-8) = 0 := by decide +kernel

/-- A combat fixture whose attacks always injure when they connect. -/
def strongHero : Being := ⟨"Strong fixture", 20, 20, 20, 20, [(.broadsword, 20)], .broadsword, .none, 0⟩

/-- An opponent that cannot attack; it can still dodge and prolong a fight. -/
def harmlessFoe : Being := ⟨"Harmless fixture", 1, 0, 0, 0, [], .punch, .none, 0⟩

/-- A completed fight preserves the surviving hero's current HP. -/
example : (combatDistribution fixtureRules strongHero 3 []).mass (· == .won 3) = 1 := by decide +kernel

/-- A dead hero cannot win, even against an empty foe list. -/
example : (combatDistribution fixtureRules strongHero 0 []).mass (· == .died) = 1 := by decide +kernel

/- A fight where neither side can attack is nonterminating, not a defeat. -/
#guard (combatDistribution fixtureRules harmlessFoe 1 [harmlessFoe]).mass (· == .stalled) == 1

-- This runs the exact solver, including elimination of missed attacks and dodges.
#guard (combatDistribution fixtureRules strongHero 3 [harmlessFoe]).mass (· == .won 3) == 1

end Rpg.Probability
