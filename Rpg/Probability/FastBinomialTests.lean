import Rpg.Probability.FastBinomial

/-! Differential checks keep the original integer evaluator explicit so compiler
simplification cannot replace both sides with the same implementation. -/
namespace Rpg.Probability.Confidence.Fast

/-- Check endpoint, signed, and interior parameters against the original count evaluator. -/
def matchesReference : Bool :=
  ([0, 1/8, 1/3, 1/2, 3/4, 1, -1/2, 3/2] : List Rat).all fun p =>
    (List.range 13).all fun n =>
      ([[], [1], [0, 1], [2, -3, 4, 0, 7], List.replicate 15 1] : List (List Int)).all fun values =>
        fastExactExpectation p n values ==
          (integerExpectation p.num p.den n values : Rat) / (p.den : Rat)^n

#guard matchesReference

/-- Endpoint fallback preserves the exact deterministic success law. -/
example : fastExactExpectation 1 2 [3, 5, 7, 9] = 7 := by decide +kernel

/-- A signed count table retains its expectation under a fair coin. -/
example : fastExactExpectation (1/2) 2 [2, -3, 4] = 0 := by decide +kernel

end Rpg.Probability.Confidence.Fast
