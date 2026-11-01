import Rpg.Probability.FastBinomial

/-!
# Tests of the fast binomial expectation

Compare `fastExactExpectation` with the slow integer function on many inputs. The test calls
`integerExpectation` by name, so the `@[csimp]` theorems do not change both sides into the same
function.
-/
namespace Rpg.Probability.Confidence.Fast

/-- The fast function gives the same value as the slow one, for chances at 0, at 1, between them and
outside them, and for tables with negative values. -/
def matchesReference : Bool :=
  ([0, 1/8, 1/3, 1/2, 3/4, 1, -1/2, 3/2] : List Rat).all fun p =>
    (List.range 13).all fun n =>
      ([[], [1], [0, 1], [2, -3, 4, 0, 7], List.replicate 15 1] : List (List Int)).all fun values =>
        fastExactExpectation p n values ==
          (integerExpectation p.num p.den n values : Rat) / (p.den : Rat)^n

#guard matchesReference

-- With success chance 1, both trials succeed, so the value is the entry for 2 successes.
example : fastExactExpectation 1 2 [3, 5, 7, 9] = 7 := by decide +kernel

-- With success chance 1/2 and 2 trials: 2/4 - 3/2 + 4/4 = 0.
example : fastExactExpectation (1/2) 2 [2, -3, 4] = 0 := by decide +kernel

end Rpg.Probability.Confidence.Fast
