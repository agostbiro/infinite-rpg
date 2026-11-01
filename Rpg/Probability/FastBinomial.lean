import Rpg.Probability.Binomial

/-!
# A faster binomial expectation

`exactExpectation` (in `Binomial.lean`) blends the table of values once for each trial, so it
needs about `n` times the table length steps. `fastExactExpectation` needs one step for each table
entry. It uses the binomial coefficients, each one got from the one before.

The `@[csimp]` theorems prove that each fast function is equal to the function it replaces. Then
the compiler runs the fast function in its place, so the compiled balance check is faster. The
proofs about `exactExpectation` stay true, because the two functions are equal. All values are
exact rationals.
-/
namespace Rpg.Probability.Confidence.Fast

/-- The binomial coefficient "`n` choose `k`", as a rational. Each one is got from the one before. -/
def coeff (n : Nat) : Nat → Rat
  | 0 => 1
  | k+1 => coeff n k * ((n : Rat) - (k : Rat)) / ((k : Rat)+1)

/-- The next coefficient times `k + 1` is this coefficient times `n - k`. -/
theorem coeff_step (n k : Nat) :
    coeff n (k+1) * ((k : Rat)+1) = coeff n k * ((n : Rat)-(k : Rat)) := by
  have hk : (0 : Rat) ≤ (k : Rat) := Rat.natCast_nonneg
  have nz : (k : Rat)+1 ≠ 0 := by grind
  exact Rat.div_mul_cancel nz

/-- Pascal's rule: a coefficient for `n + 1` trials is the sum of two coefficients for `n` trials. -/
theorem coeff_pascal (n k : Nat) :
    coeff (n+1) (k+1) = coeff n (k+1) + coeff n k := by
  induction k with
  -- The first positive count equals the number of trials.
  | zero =>
    simp [coeff, Rat.natCast_add]
    grind
  -- Apply the ratio identities, then cancel the positive count.
  | succ k ih =>
    have a := coeff_step (n+1) (k+1)
    have b := coeff_step n (k+1)
    have c := coeff_step n k
    have hk : (0 : Rat) ≤ (k : Rat) := Rat.natCast_nonneg
    simp only [Rat.natCast_add, Rat.natCast_ofNat] at *
    have eq : coeff (n+1) (k+1+1) * ((k : Rat)+1+1) =
        (coeff n (k+1+1) + coeff n (k+1)) * ((k : Rat)+1+1) := by grind
    have nz : (k : Rat)+1+1 ≠ 0 := by grind
    calc
      coeff (n+1) (k+1+1) = coeff (n+1) (k+1+1) * ((k : Rat)+1+1) / ((k : Rat)+1+1) :=
        (Rat.mul_div_cancel nz).symm
      _ = (coeff n (k+1+1) + coeff n (k+1)) * ((k : Rat)+1+1) / ((k : Rat)+1+1) := congrArg (· / ((k : Rat)+1+1)) eq
      _ = coeff n (k+1+1) + coeff n (k+1) := Rat.mul_div_cancel nz

/-- With 0 trials, the coefficient for 1 or more successes is 0. -/
theorem coeff_zero_succ (k : Nat) : coeff 0 (k+1) = 0 := by
  induction k with
  -- The first positive coefficient contains a zero factor.
  | zero =>
    simp only [coeff]
    decide +kernel
  -- Every subsequent coefficient retains that zero factor.
  | succ k ih =>
    rw [coeff, ih]
    grind

/-- The weight of `j` successes in `n` trials, for success weight `a` and failure weight `q`. It is
the binomial probability times `(a + q) ^ n`. -/
def weight (a q : Rat) (n j : Nat) : Rat := q^n * coeff n j * (a/q)^j

/-- The weight of 0 successes is `q ^ n`: every trial fails. -/
theorem weight_first (a q : Rat) (n : Nat) : weight a q n 0 = q^n := by
  simp [weight, coeff]

/-- With 0 trials, the weight of 1 or more successes is 0. -/
theorem weight_zero_succ (a q : Rat) (j : Nat) : weight a q 0 (j+1) = 0 := by
  simp [weight, coeff_zero_succ]

/-- One more trial multiplies the weight of 0 successes by `q`. -/
theorem weight_first_step (a q : Rat) (n : Nat) :
    weight a q (n+1) 0 = q * weight a q n 0 := by
  simp [weight_first, Rat.pow_succ, Rat.mul_comm]

/-- Pascal's rule for weights: the last trial either fails (times `q`) or succeeds (times `a`). -/
theorem weight_pascal (a q : Rat) (hq : q ≠ 0) (n j : Nat) :
    weight a q (n+1) (j+1) = q*weight a q n (j+1)+a*weight a q n j := by
  have cancel : a/q*q = a := Rat.div_mul_cancel hq
  simp only [weight, coeff_pascal, Rat.pow_succ]
  grind

/-- The next weight is this weight times one ratio. The fast function uses this step. -/
theorem weight_next (a q : Rat) (n j : Nat) :
    weight a q n (j+1) =
      weight a q n j * (((n : Rat)-(j : Rat))/((j : Rat)+1)*(a/q)) := by
  have hj : (0 : Rat) ≤ (j : Rat) := Rat.natCast_nonneg
  have nz : (j : Rat)+1 ≠ 0 := by grind
  have ratio := coeff_step n j
  have divcancel : (((n : Rat)-(j : Rat))/((j : Rat)+1))*((j : Rat)+1) =
      (n : Rat)-(j : Rat) := Rat.div_mul_cancel nz
  have eq : weight a q n (j+1)*((j : Rat)+1) =
      (weight a q n j * (((n : Rat)-(j : Rat))/((j : Rat)+1)*(a/q)))*((j : Rat)+1) := by
    simp only [weight, Rat.pow_succ]
    grind
  calc
    _ = weight a q n (j+1)*((j : Rat)+1)/((j : Rat)+1) := (Rat.mul_div_cancel nz).symm
    _ = _ := congrArg (· / ((j : Rat)+1)) eq
    _ = _ := Rat.mul_div_cancel nz

/-- The sum of each table value times its weight, with the first value at index `j`. -/
def weightedSum (w : Nat → Rat) : Nat → List Int → Rat
  | _, [] => 0
  | j, x::xs => w j*(x : Rat)+weightedSum w (j+1) xs

/-- The tail form of `weighted_blend`: one blend, from index `j + 1`, moves one term to the edge. -/
theorem weighted_blend_tail (a b : Int) (u v : Nat → Rat)
    -- Every later weight has failure and success contributions.
    (step : ∀ j, u (j+1) = ((b : Rat)-(a : Rat))*v (j+1)+(a : Rat)*v j)
    (values : List Int) (j : Nat) :
    weightedSum u (j+1) values = weightedSum v (j+1) (blend a b values) +
      (a : Rat)*v j*(values.getD 0 0 : Rat) := by
  induction values generalizing j with
  -- Empty tables have no boundary contribution.
  | nil =>
    simp [weightedSum, blend]
    decide +kernel
  -- Separate the first entry and apply the shifted induction hypothesis.
  | cons x xs ih =>
    simp only [weightedSum, blend, List.getD_cons_zero]
    rw [step, ih (j+1)]
    simp
    grind

/-- Blending the table once is the same as one more trial in the weights. -/
theorem weighted_blend (a b : Int) (u v : Nat → Rat)
    -- The first weight has only the failure contribution.
    (first : u 0 = ((b : Rat)-(a : Rat))*v 0)
    -- Every later weight has failure and success contributions.
    (step : ∀ j, u (j+1) = ((b : Rat)-(a : Rat))*v (j+1)+(a : Rat)*v j)
    (values : List Int) :
    weightedSum u 0 values = weightedSum v 0 (blend a b values) := by
  cases values with
  -- Both sides vanish for the empty table.
  | nil => rfl
  -- Combine the first entry with the tail boundary term.
  | cons x xs =>
    simp only [weightedSum, blend]
    rw [first, weighted_blend_tail a b u v step xs 0]
    simp
    grind

/-- With 0 trials, the weighted sum is the first table value. -/
theorem weighted_zero (a q : Rat) (values : List Int) :
    weightedSum (weight a q 0) 0 values = (values.getD 0 0 : Rat) := by
  have tail : ∀ (xs : List Int) (j : Nat), weightedSum (weight a q 0) (j+1) xs = 0 := by
    intro xs
    induction xs with
    -- An empty tail contributes zero.
    | nil =>
      intro j
      rfl
    -- Every positive-index coefficient vanishes.
    | cons x xs ih =>
      intro j
      rw [weightedSum, weight_zero_succ, ih (j+1)]
      grind
  cases values with
  -- Both sides vanish for the empty table.
  | nil => rfl
  -- Combine the first entry with the tail boundary term.
  | cons x xs =>
    rw [weightedSum, weight_first, tail xs 0]
    simp
    grind

/-- The weighted sum is equal to the integer function `integerExpectation` from `Binomial.lean`. -/
theorem integer_eq_weighted (a b : Int) (hq : (b : Rat)-(a : Rat) ≠ 0)
    (n : Nat) (values : List Int) :
    (integerExpectation a b n values : Rat) =
      weightedSum (weight (a : Rat) ((b : Rat)-(a : Rat)) n) 0 values := by
  induction n generalizing values with
  -- Both evaluators read the first entry with no trials.
  | zero => exact (weighted_zero _ _ _).symm
  -- Replace one blend with Pascal's weight recurrence.
  | succ n ih =>
    rw [integerExpectation, ih]
    exact (weighted_blend a b _ _ (weight_first_step _ _ n)
      (weight_pascal _ _ hq n) values).symm

/-- Add up the table values times their weights. Each weight is got from the one before. -/
def sumLoop (a q : Rat) (n : Nat) : Nat → Rat → Rat → List Int → Rat
  | _, _, acc, [] => acc
  | j, term, acc, x::xs =>
      sumLoop a q n (j+1)
        (term * (((n : Rat)-(j : Rat))/((j : Rat)+1)*(a/q)))
        (acc+term*(x : Rat)) xs

/-- `sumLoop` adds the weighted sum of the rest of the table to `acc`. -/
theorem sumLoop_correct (a q : Rat) (n : Nat) (values : List Int) (j : Nat) (acc : Rat) :
    sumLoop a q n j (weight a q n j) acc values =
      acc+weightedSum (weight a q n) j values := by
  induction values generalizing j acc with
  -- An empty table returns the accumulator.
  | nil =>
    simp [sumLoop, weightedSum]
    grind
  -- Advance one weight and one table entry.
  | cons x xs ih =>
    rw [sumLoop, ← weight_next, ih, weightedSum]
    grind

/-- The same value as `exactExpectation`, with one step for each table entry. If the success
chance is 1, it uses the slow function, because then `q` is 0. -/
def fastExactExpectation (p : Rat) (n : Nat) (values : List Int) : Rat :=
  let a : Rat := p.num
  let b : Rat := p.den
  let q := b-a
  if q = 0 then (integerExpectation p.num p.den n values : Rat) / b^n
  else sumLoop a q n 0 (q^n) 0 values / b^n

/-- The fast function is equal to `exactExpectation`, for every input. So compiled code can use it
in its place. -/
@[csimp] theorem exactExpectation_eq_fast : @exactExpectation = @fastExactExpectation := by
  funext p n values
  unfold exactExpectation fastExactExpectation
  dsimp only
  split
  -- The success chance is 1: both use the slow function.
  · rfl
  -- Any other success chance: the fast sum is equal to the slow function.
  · next h =>
    rw [← weight_first (p.num : Rat) ((p.den : Rat)-(p.num : Rat)) n, sumLoop_correct]
    simp only [Rat.zero_add]
    congr 1
    apply integer_eq_weighted
    simpa only [Rat.intCast_natCast] using h

/-- `lowerTail` with the fast function. -/
def fastLowerTail (p : Rat) (n k : Nat) : Rat :=
  fastExactExpectation p n (List.replicate (k+1) 1)

/-- `upperTail` with the fast function. -/
def fastUpperTail (p : Rat) (n : Nat) : Nat → Rat
  | 0 => 1
  | k+1 => 1-fastLowerTail p n k

/-- The fast lower tail is equal to `lowerTail`, so compiled code can use it in its place. -/
@[csimp] theorem lowerTail_eq_fast : @lowerTail = @fastLowerTail := by
  funext p n k
  unfold lowerTail fastLowerTail
  rw [exactExpectation_eq_fast]

/-- The fast upper tail is equal to `upperTail`, so compiled code can use it in its place. -/
@[csimp] theorem upperTail_eq_fast : @upperTail = @fastUpperTail := by
  funext p n k
  cases k with
  -- Every count is at least zero.
  | zero => rfl
  -- Preserve the complement relation for positive counts.
  | succ k => simp only [upperTail, fastUpperTail, lowerTail_eq_fast]

end Rpg.Probability.Confidence.Fast
