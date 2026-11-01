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
def fairnessTolerance : Rat := 1 / 20

/-- Historical saves retain their recorded, wider tolerance. -/
def legacyFairnessTolerance : Rat := 1 / 5

/-- Versioned observation meaning and confidence level for statistical admission. -/
inductive AdmissionProtocol where
  | legacyPoint
  | twoEventWindow
  deriving Repr, BEq, DecidableEq

/-- The fairness policy: a versioned target curve and its tolerance. -/
structure FairnessPolicy where
  retention : Rat
  shape : Nat
  tolerance : Rat
  protocol : AdmissionProtocol := .legacyPoint
  deriving Repr

/-- The policy in use. A change to these constants changes what every Adventure must pass. -/
def defaultPolicy : FairnessPolicy :=
  ⟨weibullRetention, weibullShape, legacyFairnessTolerance, .legacyPoint⟩

/-- Exploration policy requested by the player: a discrete median of ten scene choices.
The rational retention approximates 2^(-1/100); the tolerance is unchanged. -/
def explorationPolicy : FairnessPolicy :=
  ⟨99309 / 100000, 2, legacyFairnessTolerance, .legacyPoint⟩

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
def Difficulty.legacyPolicy : Difficulty → FairnessPolicy
  | .easy => ⟨993092495 / 1000000000, 2, legacyFairnessTolerance, .legacyPoint⟩
  | .medium => ⟨988032459 / 1000000000, 2, legacyFairnessTolerance, .legacyPoint⟩
  | .hard => ⟨977237220 / 1000000000, 2, legacyFairnessTolerance, .legacyPoint⟩

/-- New Wishes test two-event death windows with a five-percentage-point band. -/
def Difficulty.policy (d : Difficulty) : FairnessPolicy :=
  { d.legacyPolicy with tolerance := fairnessTolerance, protocol := .twoEventWindow }

/-- Save the curve version so a later load checks the same selected difficulty. -/
def Difficulty.profile (d : Difficulty) : String := "difficulty-" ++ d.key ++ "-v2"

/-- Decode a difficulty profile; legacy policies are handled separately. -/
def Difficulty.ofProfile : String → Option Difficulty
  | "difficulty-easy-v1" => some .easy
  | "difficulty-medium-v1" => some .medium
  | "difficulty-hard-v1" => some .hard
  | "difficulty-easy-v2" => some .easy
  | "difficulty-medium-v2" => some .medium
  | "difficulty-hard-v2" => some .hard
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

/-- Probability of death within the next two turns, conditional on being alive after t. -/
def FairnessPolicy.deathWithinTwo (p : FairnessPolicy) (t : Nat) : Rat :=
  1 - p.survival (t + 2) / p.survival t

/-- The conditional probability tested by the recorded protocol. -/
def FairnessPolicy.deathTarget (p : FairnessPolicy) (t : Nat) : Rat :=
  match p.protocol with
  | .legacyPoint => p.deathAtTwo t
  | .twoEventWindow => p.deathWithinTwo t

/-- New window tests use 95% confidence; historical point tests retain 90%. -/
def FairnessPolicy.testRisk (p : FairnessPolicy) : Rat :=
  match p.protocol with
  | .legacyPoint => 1/10
  | .twoEventWindow => 1/20

/-- Both supported confidence levels have a strictly positive error risk below one. -/
theorem FairnessPolicy.testRisk_valid (p : FairnessPolicy) :
    0 < p.testRisk ∧ p.testRisk < 1 := by
  cases h : p.protocol <;> simp [FairnessPolicy.testRisk, h] <;> decide +kernel

/-- The new difficulty policy fixes the complete requested statistical protocol. -/
theorem difficulty_conditional_band (d : Difficulty) :
    d.policy.tolerance = 1/20 ∧
    d.policy.testRisk = 1/20 ∧
    d.policy.protocol = .twoEventWindow := by
  cases d <;> decide +kernel

/-- Survival obtained by chaining risks over disjoint two-event windows. -/
def survivalThroughPairs (risk : Nat → Rat) : Nat → Rat
  | 0 => 1
  | n+1 => survivalThroughPairs risk n * (1 - risk (2*n))

/-- Exact conditional risks determine survival at all even times, including ten. -/
theorem survivalThroughPairs_eq (survival risk : Nat → Rat)
    -- Every game starts alive.
    (initial : survival 0 = 1)
    -- Each pair of choices has the stated conditional survival probability.
    (step : ∀ n, survival (2*(n+1)) = survival (2*n) * (1 - risk (2*n))) :
    ∀ n, survivalThroughPairs risk n = survival (2*n) := by
  intro n
  induction n with
  | zero => exact initial.symm
  | succ n ih =>
    rw [survivalThroughPairs, ih, step n]

/-- Conditional survival is the ratio of successive survival probabilities. -/
theorem conditional_survival_step (current next : Rat) (alive : current ≠ 0) :
    current * (1 - (1 - next / current)) = next := by
  have cancel : (1 - (1 - next / current)) = next / current := by grind
  rw [cancel, Rat.mul_comm, Rat.div_mul_cancel alive]

/-- Ratios over five consecutive pairs recover the probability of survival at ten. -/
theorem conditional_windows_at_ten (survival : Nat → Rat)
    (initial : survival 0 = 1)
    (alive : ∀ n, survival (2*n) ≠ 0) :
    survivalThroughPairs (fun t => 1 - survival (t+2) / survival t) 5 = survival 10 := by
  apply survivalThroughPairs_eq survival _ initial
  intro n
  have index : 2*(n+1) = 2*n+2 := by omega
  rw [index]
  exact (conditional_survival_step _ _ (alive n)).symm

/-- The five reference windows give exactly the reference survival at ten. -/
theorem difficulty_windows_at_ten (d : Difficulty) :
    survivalThroughPairs d.policy.deathWithinTwo 5 = d.policy.survival 10 := by
  cases d <;> decide +kernel

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
example : (FairnessPolicy.mk (1 / 2) 1 0 .legacyPoint).deathAtTwo 3 = 1 / 4 := by decide +kernel

end Rpg.Probability
