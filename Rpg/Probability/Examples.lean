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

/-- A lethal graph kills with certainty on turn two. -/
def lethalGraph : Graph where
  start := .scene 0 1
  step node := match node with
    | .scene 0 _ => pure (.scene 1 1)
    | .scene _ _ => pure .dead
    | .dead => pure .dead
    | .ended => pure .ended
    | .stalled => pure .stalled
    | .resuming => pure .stalled

/-- Exact two-turn death is certain in the bad graph. -/
theorem lethalGraph_death : lethalGraph.deathAtTwo 0 = some 1 := by decide +kernel

/-- A certain death on turn one is rejected by the first-turn guard. -/
def instantDeathGraph : Graph where
  start := .scene 0 1
  step node := match node with
    | .ended => pure .ended
    | .stalled => pure .stalled
    | _ => pure .dead

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
