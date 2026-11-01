import Rpg.Probability.StatisticalAdmission
import Rpg.Probability.TestStory
import Rpg.Probability.Examples

/-! Regression tests for window endpoints, survival conditioning and strict admission. -/
namespace Rpg.Probability
open Confidence

/-- A three-window accumulator, including first-turn and ten-turn observations. -/
def emptyWindowCounts : ValidationCounts := ⟨#[0,0,0,0,0], #[0,0,0,0,0], 1, false⟩

/-- A death on the next choice belongs to the two-choice window. -/
example : (emptyWindowCounts.observeTrace 3 Difficulty.easy.policy ⟨.dead, 1⟩).deaths =
    #[1,1,0,0,1] := by decide +kernel

/-- A death at the second choice belongs to both overlapping windows, exactly once each. -/
example : (emptyWindowCounts.observeTrace 3 Difficulty.easy.policy ⟨.dead, 2⟩).deaths =
    #[0,1,1,0,1] := by decide +kernel

/-- Death before the conditioning time cannot enter that row's denominator. -/
example : (emptyWindowCounts.observeTrace 3 Difficulty.easy.policy ⟨.dead, 2⟩).trials =
    #[1,1,1,0,1] := by decide +kernel

/-- Successful endings remain survivors at later times. -/
example : (emptyWindowCounts.observeTrace 3 Difficulty.easy.policy ⟨.ended, 1⟩).trials =
    #[1,1,1,1,1] := by decide +kernel

/-- Death exactly at ten is counted; death at eleven is excluded from the cumulative row. -/
example : (emptyWindowCounts.observeTrace 3 Difficulty.easy.policy ⟨.dead, 10⟩).deaths[4]! = 1 ∧
    (emptyWindowCounts.observeTrace 3 Difficulty.easy.policy ⟨.dead, 11⟩).deaths[4]! = 0 := by
  decide +kernel

/-- Recovering exact counts must not double-count deaths in overlapping windows. -/
example : (ValidationCounts.mk #[1,1,1,0,1] #[0,1,1,0,1] 1 false).deathsPerTurn
    Difficulty.easy.policy = #[0,1,0,0] := by decide +kernel

/-- The graph agrees with the sampler about successful endings and immediate deaths. -/
example : safeGraph.deathWithinTwo 5 = some 0 ∧
    instantDeathGraph.deathWithinTwo 0 = some 1 ∧
    instantDeathGraph.deathAtTwo 0 = some 0 := by decide +kernel

/-- New and historical budgets are explicit and immutable during a test. -/
example : validationGamesFor Difficulty.hard.policy = 5000 ∧
    validationGamesFor Difficulty.hard.legacyPolicy = 1000 ∧
    validationRows 9 Difficulty.hard.policy = 11 := by decide +kernel

-- A complete, precise observation can pass the narrow band.
#guard decide (acceptsCount ⟨1/2, 1/20⟩ (1/20) ⟨1000,500⟩)

-- A frequency inside the band still fails when its interval crosses a band edge.
#guard !decide (acceptsCount ⟨1/2, 1/20⟩ (1/20) ⟨1000,540⟩)

-- Sparse observations cannot certify the band even when the observed frequency is ideal.
#guard !decide (acceptsCount ⟨1/2, 1/20⟩ (1/20) ⟨20,10⟩)

-- Old acceptance cannot be used as new evidence for the same frequency.
#guard decide (acceptsCount ⟨1/2, 1/5⟩ (1/10) ⟨1000,600⟩) &&
  !decide (acceptsCount ⟨1/2, 1/20⟩ (1/20) ⟨1000,600⟩)

/-- A real safe adventure must fail the new ten-turn target even with a short window. -/
def strictSafeCandidate : StatisticalCandidate :=
  { TestStory.safeCandidate with policy := Difficulty.easy.policy }

#guard (sampleCounts strictSafeCandidate 7 20).trials == #[20,20,20]
#guard (sampleCounts strictSafeCandidate 7 20).deaths == #[0,0,0]
#guard !decide (ValidationAccepted 1
  ⟨#[5000,5000,5000], #[0,0,0], 5000, false⟩ Difficulty.easy.policy)

end Rpg.Probability
