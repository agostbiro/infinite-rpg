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

/-- The fairness policy: the target curve and the tolerance. Every Adventure uses the same one. -/
structure FairnessPolicy where
  retention : Rat
  shape : Nat
  tolerance : Rat
  deriving Repr

/-- The policy in use. A change to these constants changes what every Adventure must pass. -/
def defaultPolicy : FairnessPolicy :=
  ⟨weibullRetention, weibullShape, fairnessTolerance⟩

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
