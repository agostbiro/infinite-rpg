import Rpg.Probability.Examples
namespace Rpg.Probability

/-- Safe play has zero active probability after its first turn. -/
theorem safe_active (n : Nat) : safeGraph.activeAt (n+1) = 0 := by
  rw [Graph.activeAt, safeGraph_after]
  decide +kernel

/-- Every positive-horizon termination tail sum is exactly one. -/
theorem safe_partial (n : Nat) : safeGraph.terminationPartial (n+1) = 1 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    simp only [Graph.terminationPartial, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.add_zero] at *
    rw [safe_active, Rat.add_zero]
    exact ih

/-- The full expected termination time is exactly one, not just a truncated estimate. -/
theorem safe_expected_termination : safeGraph.expectedTimeToTermination.Equals 1 := by
  intro bound
  constructor
  · intro h
    have h1 := h 1
    have eq1 := safe_partial 0
    change safeGraph.terminationPartial 1 ≤ bound at h1
    rw [eq1] at h1
    exact h1
  · intro h n
    cases n with
    | zero =>
      change (0 : Rat) ≤ bound
      exact Rat.le_trans (by decide +kernel : (0 : Rat) ≤ 1) h
    | succ n =>
      change safeGraph.terminationPartial (n+1) ≤ bound
      rw [safe_partial]
      exact h

/-- Safe play has no deaths at any turn. -/
theorem safe_dead (n : Nat) : safeGraph.deadBy n = 0 := by
  cases n with
  | zero => decide +kernel
  | succ n =>
    rw [Graph.deadBy, safeGraph_after]
    decide +kernel

/-- Death-time tail sums grow by one at every turn, including after success. -/
theorem safe_deathPartial (n : Nat) : safeGraph.deathPartial n = (n : Rat) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    simp only [Graph.deathPartial, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.add_zero] at *
    rw [safe_dead]
    change safeGraph.deathPartial n + (1 - 0) = ((n + 1 : Nat) : Rat)
    change safeGraph.deathPartial n = (n : Rat) at ih
    have one : (1 - 0 : Rat) = 1 := by decide +kernel
    rw [ih, one, Rat.natCast_add]
    rfl

/-- Safe successful play has infinite unconditional expected time to death. -/
theorem safe_expected_death_infinite : safeGraph.expectedTimeToDeath.IsInfinite := by
  intro bound h
  have hp := h (bound.floor.toNat + 1)
  change safeGraph.deathPartial (bound.floor.toNat + 1) ≤ bound at hp
  rw [safe_deathPartial] at hp
  have hf := Rat.floor_monotone hp
  rw [← Rat.intCast_natCast, Rat.floor_intCast] at hf
  omega

end Rpg.Probability
