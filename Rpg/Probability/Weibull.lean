import Rpg.Probability.Distribution

/-!
A positive-integer, type-I discrete Weibull lifetime has survival
`P(T > t) = q^(t^shape)`. The integer shape keeps every finite probability exact.
These defaults are editable game-design choices, not empirical RPG standards.

## Difficulty levels

The Player picks a difficulty level (easy, medium, or hard) before a Wish. Each level is a
`BalancePolicy`: a target curve and a tolerance of 5 points. The curves differ in how many
Characters are still alive after 10 turns: 50% on easy, 30% on medium, and 10% on hard.
An Adventure keeps its level for its whole life. An Adventure with no level is medium.
-/
namespace Rpg.Probability

/-- Weibull retention parameter q; larger values delay deaths. -/
def weibullRetention : Rat := 19 / 20

/-- Weibull shape; 1 gives a geometric lifetime, 2 gives increasing hazard. -/
def weibullShape : Nat := 2

/-- Maximum absolute difference in the conditional death probability, for `defaultPolicy`
(20 points). The difficulty levels use `difficultyTolerance` (5 points) instead. -/
def balanceTolerance : Rat := 1 / 5

/-- The balance policy: the target curve and the tolerance. Each Adventure has one: the policy of
its difficulty level. -/
structure BalancePolicy where
  retention : Rat
  shape : Nat
  tolerance : Rat
  deriving Repr, DecidableEq

/-- The old policy, from before the difficulty levels, with a tolerance of 20 points. Only the
test Adventure uses it, as an exemption (see `TestAdventure.statisticalCandidate`). -/
def defaultPolicy : BalancePolicy :=
  ⟨weibullRetention, weibullShape, balanceTolerance⟩

/-- Exclude invalid Weibull parameters and vacuous tolerances. -/
def BalancePolicy.Valid (p : BalancePolicy) : Prop :=
  0 < p.retention ∧ p.retention < 1 ∧ 0 < p.shape ∧
  0 ≤ p.tolerance ∧ p.tolerance < 1

instance (p : BalancePolicy) : Decidable p.Valid := by
  unfold BalancePolicy.Valid
  infer_instance

/-- Probability that the reference lifetime exceeds t turns. -/
def BalancePolicy.survival (p : BalancePolicy) (t : Nat) : Rat :=
  p.retention ^ (t ^ p.shape)

/-- Probability of death at exactly turn t+2, conditional on survival past t.
This is not the probability of death anywhere within the next two turns. -/
def BalancePolicy.deathAtTwo (p : BalancePolicy) (t : Nat) : Rat :=
  (p.survival (t + 1) - p.survival (t + 2)) / p.survival t

/-- Probability of death within the next two turns, for comparison. -/
def BalancePolicy.deathWithinTwo (p : BalancePolicy) (t : Nat) : Rat :=
  1 - p.survival (t + 2) / p.survival t

/-- The chosen default parameters define a nondegenerate policy. -/
theorem defaultPolicy_valid : defaultPolicy.Valid := by decide +kernel

/-! ## Difficulty levels -/

/-- How dangerous an Adventure is. The Player picks it before a Wish, and it stays the same for
the life of the Adventure. -/
inductive DifficultyLevel where
  | easy
  | medium
  | hard
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Every difficulty level, from the safest to the most dangerous. -/
def DifficultyLevel.all : List DifficultyLevel := [.easy, .medium, .hard]

/-- The name of a level in JSON, in `adventure.json` and in the body of `/api/wish`. -/
def DifficultyLevel.key : DifficultyLevel → String
  | .easy => "easy"
  | .medium => "medium"
  | .hard => "hard"

/-- The level with JSON name `key`, or `none` if no level has that name. -/
def DifficultyLevel.ofKey? (key : String) : Option DifficultyLevel :=
  DifficultyLevel.all.find? (·.key == key)

/-- The chance to be alive after 10 turns that each level aims at: 50%, 30%, or 10%. -/
def DifficultyLevel.survivalAtTen : DifficultyLevel → Rat
  | .easy => 1 / 2
  | .medium => 3 / 10
  | .hard => 1 / 10

/-- The Weibull retention q of each level. Each value is `survivalAtTen ^ (1/100)`, rounded down
to 9 decimal places, so that `q ^ (10 ^ 2)` is just under `survivalAtTen`. -/
def DifficultyLevel.retention : DifficultyLevel → Rat
  | .easy => 993092495 / 1000000000
  | .medium => 988032459 / 1000000000
  | .hard => 977237220 / 1000000000

/-- The Weibull shape of every level. With shape 2, the danger rises on each turn. -/
def difficultyShape : Nat := 2

/-- The tolerance of every level: 5 points. It is not `balanceTolerance`, which belongs to
`defaultPolicy`. -/
def difficultyTolerance : Rat := 1 / 20

/-- The balance policy of a level: its curve, and a tolerance of 5 points. -/
def DifficultyLevel.policy (level : DifficultyLevel) : BalancePolicy :=
  ⟨level.retention, difficultyShape, difficultyTolerance⟩

/-- The level whose policy is `policy`, or `none` if no level has it (for example `defaultPolicy`). -/
def DifficultyLevel.ofPolicy? (policy : BalancePolicy) : Option DifficultyLevel :=
  DifficultyLevel.all.find? (·.policy == policy)

-- Each level reads back from its JSON name, and no other name reads as a level.
#guard DifficultyLevel.all.all fun level => DifficultyLevel.ofKey? level.key == some level
#guard DifficultyLevel.ofKey? "Medium" == none
#guard DifficultyLevel.ofKey? "" == none
-- Each level is found again from its policy, and the default policy is not a level.
#guard DifficultyLevel.all.all fun level => DifficultyLevel.ofPolicy? level.policy == some level
#guard DifficultyLevel.ofPolicy? defaultPolicy == none

/-- Every level is a valid policy: 0 < q < 1, a positive shape, and a tolerance from 0 to 1. -/
theorem difficulty_valid (level : DifficultyLevel) : level.policy.Valid := by
  cases level <;> decide +kernel

/-- At turn 10, more Characters are alive on easy than on medium, and more on medium than on
hard. -/
theorem difficulty_order :
    -- Hard is more dangerous than medium.
    DifficultyLevel.hard.policy.survival 10 < DifficultyLevel.medium.policy.survival 10 ∧
    -- Medium is more dangerous than easy.
    DifficultyLevel.medium.policy.survival 10 < DifficultyLevel.easy.policy.survival 10 := by
  decide +kernel

/-- The curve of each level is within one millionth below its target at turn 10. -/
theorem difficulty_survival_at_ten (level : DifficultyLevel) :
    -- The curve is at most one millionth below the target.
    level.survivalAtTen - 1 / 1000000 < level.policy.survival 10 ∧
    -- The curve is not above the target.
    level.policy.survival 10 ≤ level.survivalAtTen := by
  cases level <;> decide +kernel

/-- Each level has a tolerance of 5 points. -/
example (level : DifficultyLevel) : level.policy.tolerance = 1 / 20 := by
  cases level <;> rfl

/-- The levels are not the default policy: it has a tolerance of 20 points. -/
example : DifficultyLevel.medium.policy ≠ defaultPolicy := by decide +kernel

/-- The reference lifetime starts alive with probability one. -/
example : defaultPolicy.survival 0 = 1 := by decide +kernel

/-- At t=0, death at exactly turn 2 is the chance to live through turn 1 and die on turn 2:
S(1) - S(2) = q - q^4. -/
example : defaultPolicy.deathAtTwo 0 = (19 / 20 : Rat) - (19 / 20) ^ 4 := by decide +kernel

/-- With shape 2 the danger rises: death at t+2 is more likely at t = 3 than at t = 0. -/
example : defaultPolicy.deathAtTwo 0 < defaultPolicy.deathAtTwo 3 := by decide +kernel

/-- A geometric reference has a constant two-turn conditional point probability. -/
example : (BalancePolicy.mk (1 / 2) 1 0).deathAtTwo 3 = 1 / 4 := by decide +kernel

end Rpg.Probability
