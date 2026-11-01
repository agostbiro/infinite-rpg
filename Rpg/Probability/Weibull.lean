import Rpg.Probability.Distribution

/-!
A positive-integer, type-I discrete Weibull lifetime has survival
`P(T > t) = q^(t^shape)`. The integer shape keeps every finite probability exact.
These defaults are editable game-design choices, not empirical RPG standards.
-/
namespace Rpg.Probability

/-- Weibull retention parameter q; larger values delay deaths. -/
def weibullRetention : Rat := 19 / 20

/-- Weibull shape; 1 gives a geometric lifetime, 2 gives increasing hazard. -/
def weibullShape : Nat := 2

/-- Maximum absolute difference in the conditional death probability. -/
def fairnessTolerance : Rat := 1 / 5

/-- The fairness policy: a versioned target curve and its tolerance. -/
structure FairnessPolicy where
  retention : Rat
  shape : Nat
  tolerance : Rat
  deriving Repr

/-- The policy in use. A change to these constants changes what every Adventure must pass. -/
def defaultPolicy : FairnessPolicy :=
  ⟨weibullRetention, weibullShape, fairnessTolerance⟩

/-- Exploration policy requested by the player: a discrete median of ten scene choices.
The rational retention approximates 2^(-1/100); the tolerance is unchanged. -/
def explorationPolicy : FairnessPolicy :=
  ⟨99309 / 100000, 2, fairnessTolerance⟩

/-- The difficulty selected before generating a new adventure. -/
inductive Difficulty where
  | easy | medium | hard
  deriving Repr, BEq, DecidableEq

/-- Stable names used by the form and JSON API. -/
def Difficulty.key : Difficulty → String
  | .easy => "easy"
  | .medium => "medium"
  | .hard => "hard"

/-- Decode only the three supported difficulty names. -/
def Difficulty.ofKey : String → Option Difficulty
  | "easy" => some .easy
  | "medium" => some .medium
  | "hard" => some .hard
  | _ => none

/-- Target probability of surviving ten scene choices under the test policy. -/
def Difficulty.survivalAtTen : Difficulty → Rat
  | .easy => 1 / 2
  | .medium => 3 / 10
  | .hard => 1 / 10

/-- Shape two is fixed. Retentions approximate p^(1/100) with nine decimal places. -/
def Difficulty.policy : Difficulty → FairnessPolicy
  | .easy => ⟨993092495 / 1000000000, 2, fairnessTolerance⟩
  | .medium => ⟨988032459 / 1000000000, 2, fairnessTolerance⟩
  | .hard => ⟨977237220 / 1000000000, 2, fairnessTolerance⟩

/-- Save the curve version so a later load checks the same selected difficulty. -/
def Difficulty.profile (d : Difficulty) : String := "difficulty-" ++ d.key ++ "-v1"

/-- Decode a difficulty profile; legacy policies are handled separately. -/
def Difficulty.ofProfile : String → Option Difficulty
  | "difficulty-easy-v1" => some .easy
  | "difficulty-medium-v1" => some .medium
  | "difficulty-hard-v1" => some .hard
  | _ => none

/-- Exclude invalid Weibull parameters and vacuous tolerances. -/
def FairnessPolicy.Valid (p : FairnessPolicy) : Prop :=
  0 < p.retention ∧ p.retention < 1 ∧ 0 < p.shape ∧
  0 ≤ p.tolerance ∧ p.tolerance < 1

instance (p : FairnessPolicy) : Decidable p.Valid := by
  unfold FairnessPolicy.Valid
  infer_instance

/-- Probability that the reference lifetime exceeds t turns. -/
def FairnessPolicy.survival (p : FairnessPolicy) (t : Nat) : Rat :=
  p.retention ^ (t ^ p.shape)

/-- Probability of death at exactly turn t+2, conditional on survival past t.
This is not the probability of death anywhere within the next two turns. -/
def FairnessPolicy.deathAtTwo (p : FairnessPolicy) (t : Nat) : Rat :=
  (p.survival (t + 1) - p.survival (t + 2)) / p.survival t

/-- Probability of death within the next two turns, for comparison. -/
def FairnessPolicy.deathWithinTwo (p : FairnessPolicy) (t : Nat) : Rat :=
  1 - p.survival (t + 2) / p.survival t

/-- The chosen default parameters define a nondegenerate policy. -/
theorem defaultPolicy_valid : defaultPolicy.Valid := by decide +kernel

/-- The exploration parameters form a valid policy. -/
theorem explorationPolicy_valid : explorationPolicy.Valid := by decide +kernel

/-- The reference lifetime crosses one-half between turns nine and ten. -/
theorem explorationPolicy_median :
    (1 / 2 : Rat) < explorationPolicy.survival 9 ∧
    explorationPolicy.survival 10 ≤ (1 / 2 : Rat) := by
  decide +kernel

/-- Every difficulty defines a nondegenerate curve. -/
theorem difficulty_valid (d : Difficulty) : d.policy.Valid := by
  cases d <;> decide +kernel

/-- The rational curves meet their ten-choice survival targets to within one millionth. -/
theorem difficulty_target (d : Difficulty) :
    d.survivalAtTen - 1 / 1000000 < d.policy.survival 10 ∧
    d.policy.survival 10 ≤ d.survivalAtTen := by
  cases d <;> decide +kernel

/-- At ten choices, the reference survival strictly decreases with difficulty. -/
theorem difficulty_order :
    Difficulty.hard.policy.survival 10 < Difficulty.medium.policy.survival 10 ∧
    Difficulty.medium.policy.survival 10 < Difficulty.easy.policy.survival 10 := by
  decide +kernel

/-- The reference lifetime starts alive with probability one. -/
example : defaultPolicy.survival 0 = 1 := by decide +kernel

/-- At t=0, death at exactly turn 2 is the chance to live through turn 1 and die on turn 2:
S(1) - S(2) = q - q^4. -/
example : defaultPolicy.deathAtTwo 0 = (19 / 20 : Rat) - (19 / 20) ^ 4 := by decide +kernel

/-- With shape 2 the danger rises: death at t+2 is more likely at t = 3 than at t = 0. -/
example : defaultPolicy.deathAtTwo 0 < defaultPolicy.deathAtTwo 3 := by decide +kernel

/-- A geometric reference has a constant two-turn conditional point probability. -/
example : (FairnessPolicy.mk (1 / 2) 1 0).deathAtTwo 3 = 1 / 4 := by decide +kernel

end Rpg.Probability
