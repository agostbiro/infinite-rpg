import Rpg.Probability.Weibull

/-! A continuation keeps the age of the original Weibull curve. Subtracting exponents before
raising the rational avoids constructing two much larger powers just to divide them. -/
namespace Rpg.Probability

/-- Reference survival for another `turns` events after surviving `elapsed` events. -/
def BalancePolicy.remainingSurvival (p : BalancePolicy) (elapsed turns : Nat) : Rat :=
  p.retention ^ ((elapsed + turns) ^ p.shape - elapsed ^ p.shape)

/-- A valid Weibull reference has positive survival at every finite time. -/
theorem BalancePolicy.survival_positive (p : BalancePolicy)
    (valid : p.Valid) (t : Nat) : 0 < p.survival t :=
  Rat.pow_pos valid.1

/-- The executable continuation is exactly S(t+u)/S(t), with the original parameters. -/
theorem BalancePolicy.remainingSurvival_eq_ratio (p : BalancePolicy)
    (valid : p.Valid) (elapsed turns : Nat) :
    p.remainingSurvival elapsed turns = p.survival (elapsed + turns) / p.survival elapsed := by
  have order : elapsed ^ p.shape ≤ (elapsed + turns) ^ p.shape :=
    Nat.pow_le_pow_left (by omega) p.shape
  have factor : p.survival (elapsed + turns) =
      p.remainingSurvival elapsed turns * p.survival elapsed := by
    unfold survival remainingSurvival
    rw [← Lean.Grind.Semiring.pow_add, Nat.sub_add_cancel order]
  have nonzero : p.survival elapsed ≠ 0 := by
    have positive := p.survival_positive valid elapsed
    intro zero
    rw [zero] at positive
    exact Rat.lt_irrefl positive
  rw [factor, Rat.mul_div_cancel nonzero]

/-- A checkpoint starts alive with probability one, without resetting the curve's age. -/
theorem BalancePolicy.remainingSurvival_zero (p : BalancePolicy) (elapsed : Nat) :
    p.remainingSurvival elapsed 0 = 1 := by
  simp [remainingSurvival]

/-- Successive conditioning keeps the original curve rather than restarting it. -/
theorem BalancePolicy.remainingSurvival_compose (p : BalancePolicy) (t u v : Nat) :
    p.remainingSurvival t (u + v) =
      p.remainingSurvival t u * p.remainingSurvival (t + u) v := by
  have first : t ^ p.shape ≤ (t + u) ^ p.shape :=
    Nat.pow_le_pow_left (by omega) p.shape
  have second : (t + u) ^ p.shape ≤ (t + u + v) ^ p.shape :=
    Nat.pow_le_pow_left (by omega) p.shape
  unfold remainingSurvival
  rw [← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.add_assoc]
  omega

/-- With shape two, the residual exponent contains the age term 2*t*u. -/
theorem BalancePolicy.remainingSurvival_shape_two (p : BalancePolicy)
    (shape : p.shape = 2) (t u : Nat) :
    p.remainingSurvival t u = p.retention ^ (u ^ 2 + 2 * t * u) := by
  have square : (t + u) ^ 2 = t ^ 2 + (u ^ 2 + 2 * t * u) := by grind
  simp only [remainingSurvival, shape, square, Nat.add_sub_cancel_left]

/-- First-event death, then death anywhere in each next pair of events, at the actual age. -/
def BalancePolicy.checkpointTarget (p : BalancePolicy) (elapsed row : Nat) : Rat :=
  if row = 0 then 1 - p.remainingSurvival elapsed 1
  else 1 - p.remainingSurvival (elapsed + row - 1) 2

/-- Every pair target is the conditional Weibull probability of dying within the next two events. -/
theorem BalancePolicy.checkpointTarget_pair (p : BalancePolicy) (valid : p.Valid)
    (elapsed offset : Nat) :
    p.checkpointTarget elapsed (offset + 1) =
      1 - p.survival (elapsed + offset + 2) / p.survival (elapsed + offset) := by
  simp only [checkpointTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte]
  rw [p.remainingSurvival_eq_ratio valid]
  congr 2 <;> omega

end Rpg.Probability
