import Rpg.Probability.FastBinomial
import Rpg.Probability.Balance

/-!
Equal-tailed exact binomial intervals, represented by conservative rational endpoints.
Coverage is proved by inverting binomial tail tests. The joint sampling model allows
random qualifying counts and dependence between rows from the same fixed game batch.
-/
namespace Rpg.Probability.Confidence

/-- The exact Clopper–Pearson interval contains probabilities not rejected by either tail. -/
def BinomialContains (delta : Rat) (n k : Nat) (p : Rat) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ delta/2 ≤ lowerTail p n k ∧ delta/2 ≤ upperTail p n k

instance (delta : Rat) (n k : Nat) (p : Rat) : Decidable (BinomialContains delta n k p) := by
  unfold BinomialContains
  infer_instance

/-- The exact binomial interval misses the truth with probability at most delta. -/
theorem binomial_coverage (p delta : Rat) (n : Nat)
    -- The success probability is nonnegative.
    (hp : 0 ≤ p)
    -- The success probability is at most one.
    (hp1 : p ≤ 1)
    -- The permitted error is nonnegative.
    (hd : 0 ≤ delta) :
    binomialExpectation p n (fun k => if BinomialContains delta n k p then 0 else 1) ≤ delta := by
  have half : 0 ≤ delta/2 := by grind
  have lower := lowerTail_error p (delta/2) n hp hp1 half
  have upper := upperTail_error p (delta/2) n hp hp1 half
  have bound := monotone p hp hp1 n
    (fun k => if BinomialContains delta n k p then 0 else 1)
    (fun k => (if lowerTail p n k < delta/2 then 1 else 0) +
      (if upperTail p n k < delta/2 then 1 else 0)) (by
        intro k
        unfold BinomialContains
        split <;> split <;> split <;> grind)
  rw [add] at bound
  grind

/-- Rational endpoints enclosing the exact binomial interval. -/
structure Interval where
  lower : Rat
  upper : Rat
  deriving Repr, DecidableEq

/-- A probability lies between the reported endpoints. -/
def Interval.Contains (interval : Interval) (p : Rat) : Prop :=
  interval.lower ≤ p ∧ p ≤ interval.upper

instance (interval : Interval) (p : Rat) : Decidable (interval.Contains p) := by
  unfold Interval.Contains
  infer_instance

/-- Refine the lower endpoint, rounding outward when the search ends. -/
def lowerSearch (alpha : Rat) (n k : Nat) : Nat → Rat → Rat → Rat
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    let mid := (lo+hi)/2
    if upperTail mid n k < alpha then lowerSearch alpha n k fuel mid hi
    else lowerSearch alpha n k fuel lo mid

/-- Refine the upper endpoint, rounding outward when the search ends. -/
def upperSearch (alpha : Rat) (n k : Nat) : Nat → Rat → Rat → Rat
  | 0, _, hi => hi
  | fuel+1, lo, hi =>
    let mid := (lo+hi)/2
    if lowerTail mid n k < alpha then upperSearch alpha n k fuel lo mid
    else upperSearch alpha n k fuel mid hi

/-- Lower endpoint search never excludes a probability accepted by its tail test. -/
theorem lowerSearch_safe (alpha p : Rat) (n k fuel : Nat)
    -- The probability is nonnegative.
    (hp : 0 ≤ p)
    -- The upper-tail test accepts this probability.
    (tail : alpha ≤ upperTail p n k) (lo hi : Rat)
    -- The search starts inside the probability range.
    (lo0 : 0 ≤ lo)
    -- The search endpoints are ordered.
    (ordered : lo ≤ hi)
    -- The upper endpoint is at most one.
    (hi1 : hi ≤ 1)
    -- The initial lower endpoint does not exclude the probability.
    (start : lo ≤ p) :
    lowerSearch alpha n k fuel lo hi ≤ p := by
  induction fuel generalizing lo hi with
  -- Return the safe lower endpoint when the search ends.
  | zero => exact start
  -- Refine the search using an exact tail comparison.
  | succ fuel ih =>
    simp only [lowerSearch]
    split
    -- A rejected midpoint must lie below the accepted probability.
    · next excluded =>
      have below : (lo+hi)/2 ≤ p := by
        by_cases h : p ≤ (lo+hi)/2
        -- Monotonicity rules out a midpoint above the probability.
        · have mono := upperTail_monotone p ((lo+hi)/2) hp h (by grind) n k
          grind
        -- Otherwise the new lower endpoint is safe.
        · grind
      exact ih _ _ (by grind) (by grind) hi1 below
    -- Keeping the old lower endpoint preserves safety.
    · exact ih _ _ lo0 (by grind) (by grind) start

/-- Upper endpoint search never excludes a probability accepted by its tail test. -/
theorem upperSearch_safe (alpha p : Rat) (n k fuel : Nat)
    -- The probability is at most one.
    (hp1 : p ≤ 1)
    -- The lower-tail test accepts this probability.
    (tail : alpha ≤ lowerTail p n k) (lo hi : Rat)
    -- The search starts inside the probability range.
    (lo0 : 0 ≤ lo)
    -- The search endpoints are ordered.
    (ordered : lo ≤ hi)
    -- The upper endpoint is at most one.
    (hi1 : hi ≤ 1)
    -- The initial upper endpoint does not exclude the probability.
    (start : p ≤ hi) :
    p ≤ upperSearch alpha n k fuel lo hi := by
  induction fuel generalizing lo hi with
  -- Return the safe upper endpoint when the search ends.
  | zero => exact start
  -- Refine the search using an exact tail comparison.
  | succ fuel ih =>
    simp only [upperSearch]
    split
    -- A rejected midpoint must lie above the accepted probability.
    · next excluded =>
      have above : p ≤ (lo+hi)/2 := by
        by_cases h : (lo+hi)/2 ≤ p
        -- Monotonicity rules out a midpoint below the probability.
        · have mono := lowerTail_antitone ((lo+hi)/2) p (by grind) h hp1 n k
          grind
        -- Otherwise the new upper endpoint is safe.
        · grind
      exact ih _ _ lo0 (by grind) (by grind) above
    -- Keeping the old upper endpoint preserves safety.
    · exact ih _ _ (by grind) (by grind) hi1 start

/-- Eight exact bisections give endpoints on a grid of 1/256; rounding is always outward. -/
def intervalSteps : Nat := 8

/-- An executable exact-binomial interval with conservative rational endpoints. -/
def confidenceInterval (delta : Rat) (n k : Nat) : Interval :=
  ⟨lowerSearch (delta/2) n k intervalSteps 0 1,
   upperSearch (delta/2) n k intervalSteps 0 1⟩

/-- Every probability in the exact interval is in the reported rational enclosure. -/
theorem confidenceInterval_encloses (delta p : Rat) (n k : Nat)
    (inside : BinomialContains delta n k p) :
    (confidenceInterval delta n k).Contains p := by
  constructor
  -- The reported lower endpoint is no higher than any accepted probability.
  · exact lowerSearch_safe _ _ _ _ _ inside.1 inside.2.2.2
      0 1 (by decide) (by decide) (by decide) inside.1
  -- The reported upper endpoint is no lower than any accepted probability.
  · exact upperSearch_safe _ _ _ _ _ inside.2.1 inside.2.2.1
      0 1 (by decide) (by decide) (by decide) inside.2.1

/-- The displayed interval retains the exact binomial coverage guarantee. -/
theorem intervalConfidence (p delta : Rat) (n : Nat)
    -- The success probability is nonnegative.
    (hp : 0 ≤ p)
    -- The success probability is at most one.
    (hp1 : p ≤ 1)
    -- The permitted error is nonnegative.
    (hd : 0 ≤ delta) :
    binomialExpectation p n (fun k =>
      if (confidenceInterval delta n k).Contains p then 0 else 1) ≤ delta := by
  have bound := monotone p hp hp1 n
    (fun k => if (confidenceInterval delta n k).Contains p then 0 else 1)
    (fun k => if BinomialContains delta n k p then 0 else 1) (by
      intro k
      split
      -- A reported interval containing the truth contributes no error.
      · split <;> decide +kernel
      -- If it misses, the enclosed exact interval also misses.
      · next outside =>
        split
        -- Containment in the exact interval contradicts the reported miss.
        · next inside => exact False.elim (outside (confidenceInterval_encloses _ _ _ _ inside))
        -- Both intervals missed the truth.
        · exact Rat.le_refl)
  exact Rat.le_trans bound (binomial_coverage p delta n hp hp1 hd)

/-- A row's qualifying games and observed deaths. -/
structure Observation where
  trials : Nat
  deaths : Nat
  deriving Repr, DecidableEq

/-- A shared Weibull target and its allowed absolute deviation. -/
structure Band where
  target : Rat
  tolerance : Rat

/-- Every lower endpoint stays inside the search bracket. -/
theorem lowerSearch_bounds (alpha : Rat) (n k fuel : Nat) (lo hi : Rat)
    (ordered : lo ≤ hi) :
    lo ≤ lowerSearch alpha n k fuel lo hi ∧ lowerSearch alpha n k fuel lo hi ≤ hi := by
  induction fuel generalizing lo hi with
  -- The terminal endpoint lies in its bracket.
  | zero => simp [lowerSearch, ordered]
  -- Refine one half of the ordered bracket.
  | succ fuel ih =>
    simp only [lowerSearch]
    split
    -- The upper half retains the original bounds.
    · have h := ih ((lo+hi)/2) hi (by grind)
      grind
    -- The lower half retains the original bounds.
    · have h := ih lo ((lo+hi)/2) (by grind)
      grind

/-- Every upper endpoint stays inside the search bracket. -/
theorem upperSearch_bounds (alpha : Rat) (n k fuel : Nat) (lo hi : Rat)
    (ordered : lo ≤ hi) :
    lo ≤ upperSearch alpha n k fuel lo hi ∧ upperSearch alpha n k fuel lo hi ≤ hi := by
  induction fuel generalizing lo hi with
  -- The terminal endpoint lies in its bracket.
  | zero => simp [upperSearch, ordered]
  -- Refine one half of the ordered bracket.
  | succ fuel ih =>
    simp only [upperSearch]
    split
    -- The lower half retains the original bounds.
    · have h := ih lo ((lo+hi)/2) (by grind)
      grind
    -- The upper half retains the original bounds.
    · have h := ih ((lo+hi)/2) hi (by grind)
      grind

/-- Stop refining once the bracket decides whether the lower endpoint meets a bound. -/
def lowerMeets (alpha : Rat) (n k : Nat) (bound : Rat) : Nat → Rat → Rat → Bool
  | 0, lo, _ => decide (bound ≤ lo)
  | fuel+1, lo, hi =>
    if bound ≤ lo then true else if hi < bound then false else
    let mid := (lo+hi)/2
    if upperTail mid n k < alpha then lowerMeets alpha n k bound fuel mid hi
    else lowerMeets alpha n k bound fuel lo mid

/-- Stop refining once the bracket decides whether the upper endpoint meets a bound. -/
def upperMeets (alpha : Rat) (n k : Nat) (bound : Rat) : Nat → Rat → Rat → Bool
  | 0, _, hi => decide (hi ≤ bound)
  | fuel+1, lo, hi =>
    if hi ≤ bound then true else if bound < lo then false else
    let mid := (lo+hi)/2
    if lowerTail mid n k < alpha then upperMeets alpha n k bound fuel lo mid
    else upperMeets alpha n k bound fuel mid hi

/-- Early stopping gives exactly the original lower-endpoint comparison. -/
theorem lowerMeets_correct (alpha : Rat) (n k : Nat) (bound : Rat) (fuel : Nat)
    (lo hi : Rat) (ordered : lo ≤ hi) :
    lowerMeets alpha n k bound fuel lo hi = true ↔ bound ≤ lowerSearch alpha n k fuel lo hi := by
  induction fuel generalizing lo hi with
  -- The terminal endpoint lies in its bracket.
  | zero => simp [lowerMeets, lowerSearch]
  -- Refine one half of the ordered bracket.
  | succ fuel ih =>
    have bounds := lowerSearch_bounds alpha n k (fuel+1) lo hi ordered
    rw [lowerMeets]
    split
    -- The whole bracket already satisfies the comparison.
    · simp only [true_iff]
      grind
    -- Otherwise reject a disjoint bracket or refine it.
    · split
      · simp only [Bool.false_eq_true, false_iff]
        grind
      · rw [lowerSearch]
        split <;> rename_i branch <;> simp only [branch, ↓reduceIte] <;> apply ih <;> grind

/-- Early stopping gives exactly the original upper-endpoint comparison. -/
theorem upperMeets_correct (alpha : Rat) (n k : Nat) (bound : Rat) (fuel : Nat)
    (lo hi : Rat) (ordered : lo ≤ hi) :
    upperMeets alpha n k bound fuel lo hi = true ↔ upperSearch alpha n k fuel lo hi ≤ bound := by
  induction fuel generalizing lo hi with
  -- The terminal endpoint lies in its bracket.
  | zero => simp [upperMeets, upperSearch]
  -- Refine one half of the ordered bracket.
  | succ fuel ih =>
    have bounds := upperSearch_bounds alpha n k (fuel+1) lo hi ordered
    rw [upperMeets]
    split
    -- The whole bracket already satisfies the comparison.
    · simp only [true_iff]
      grind
    -- Otherwise reject a disjoint bracket or refine it.
    · split
      · simp only [Bool.false_eq_true, false_iff]
        grind
      · rw [upperSearch]
        split <;> rename_i branch <;> simp only [branch, ↓reduceIte] <;> apply ih <;> grind

/-- Admission requires data and the entire interval inside its policy band. -/
def acceptsCount (band : Band) (delta : Rat) (count : Observation) : Prop :=
  let interval := confidenceInterval delta count.trials count.deaths
  0 < count.trials ∧ count.deaths ≤ count.trials ∧
  band.target-band.tolerance ≤ interval.lower ∧
  interval.upper ≤ band.target+band.tolerance

instance (band : Band) (delta : Rat) (count : Observation) : Decidable (acceptsCount band delta count) := by
  let fast := 0 < count.trials ∧ count.deaths ≤ count.trials ∧
    lowerMeets (delta/2) count.trials count.deaths (band.target-band.tolerance) intervalSteps 0 1 = true ∧
    upperMeets (delta/2) count.trials count.deaths (band.target+band.tolerance) intervalSteps 0 1 = true
  have same : fast ↔ acceptsCount band delta count := by
    simp only [fast, acceptsCount, confidenceInterval,
      lowerMeets_correct _ _ _ _ _ 0 1 (by decide), upperMeets_correct _ _ _ _ _ 0 1 (by decide)]
  exact decidable_of_iff fast same

/-- A falsely accepted row must have missed the true probability. -/
theorem false_accept_misses (band : Band) (delta p : Rat) (count : Observation)
    -- The entire reported interval is inside the band.
    (accepted : acceptsCount band delta count)
    -- The true probability is outside the band.
    (outside : ¬ WithinTolerance p band.target band.tolerance) :
    ¬ (confidenceInterval delta count.trials count.deaths).Contains p := by
  intro inside
  apply outside
  exact ⟨Rat.le_trans accepted.2.2.1 inside.1, Rat.le_trans inside.2 accepted.2.2.2⟩

/-- Exact expectation under a finite joint observation law. -/
def expectation (law : Distribution α) (f : α → Rat) : Rat :=
  (law.entries.map fun (x, weight) => weight * f x).sum

/-- Nonnegative weights preserve pointwise comparisons of joint events. -/
theorem expectation_monotone (law : Distribution α)
    -- Every outcome has a nonnegative weight.
    (nonnegative : ∀ e ∈ law.entries, 0 ≤ e.2)
    (f g : α → Rat)
    -- The two statistics are ordered at each outcome.
    (h : ∀ x, f x ≤ g x) : expectation law f ≤ expectation law g := by
  unfold expectation
  generalize law.entries = entries at *
  revert nonnegative
  induction entries with
  -- An empty sum is zero on both sides.
  | nil =>
    intro _
    exact Rat.le_refl
  -- Add the ordered first term to the ordered remaining sum.
  | cons e rest ih =>
    intro nonnegative
    have hp := nonnegative e (by simp)
    have ht : ∀ e ∈ rest, 0 ≤ e.2 := by
      intro e he
      exact nonnegative e (by simp [he])
    have hr := ih ht
    have he := Rat.mul_le_mul_of_nonneg_left (h e.1) hp
    simp only [List.map_cons, List.sum_cons]
    grind

/-- A constant has that expectation under a normalized observation law. -/
theorem expectation_constant (law : Distribution α) (valid : law.Valid) (c : Rat) :
    expectation law (fun _ => c) = c := by
  have factor : ∀ entries : List (α × Rat),
      (entries.map fun e => e.2*c).sum = (entries.map Prod.snd).sum*c := by
    intro entries
    induction entries with
    -- The empty sum has no contribution.
    | nil => simp
    -- Distribute the constant over the next weight.
    | cons e rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      grind
  unfold expectation
  rw [factor, valid.2, Rat.one_mul]

/-- Each row's success count is binomial conditional on its random qualifying count.
This is the accepted sampling assumption for a fixed batch of independent games;
rows may depend on one another. -/
structure BinomialSampling (law : Distribution (Fin m → Observation)) (truth : Fin m → Rat) where
  sizes : Fin m → Distribution Nat
  sizesValid : ∀ i, (sizes i).Valid
  marginals : ∀ i (f : Observation → Rat),
    expectation law (fun observations => f (observations i)) =
      expectation (sizes i) (fun n => binomialExpectation (truth i) n (fun k => f ⟨n, k⟩))

/-- Every true expectation is within its selected Weibull tolerance band. -/
def familyBalanced (truth : Fin m → Rat) (bands : Fin m → Band) : Prop :=
  ∀ i, WithinTolerance (truth i) (bands i).target (bands i).tolerance

instance (truth : Fin m → Rat) (bands : Fin m → Band) : Decidable (familyBalanced truth bands) := by
  unfold familyBalanced
  infer_instance

/-- All observed intervals must pass the shared comparison policy. -/
def acceptsFamily (bands : Fin m → Band) (delta : Rat) (observations : Fin m → Observation) : Prop :=
  ∀ i, acceptsCount (bands i) delta (observations i)

instance (bands : Fin m → Band) (delta : Rat) (observations : Fin m → Observation) :
    Decidable (acceptsFamily bands delta observations) := by
  unfold acceptsFamily
  infer_instance

/-- The probability that one row's reported interval misses its true expectation. -/
def intervalMissProbability (law : Distribution (Fin m → Observation)) (truth : Fin m → Rat)
    (delta : Rat) (i : Fin m) : Rat :=
  expectation law fun counts =>
    if (confidenceInterval delta (counts i).trials (counts i).deaths).Contains (truth i) then 0 else 1

/-- Coverage remains valid after averaging over random qualifying sample sizes. -/
theorem rowConfidence (law : Distribution (Fin m → Observation)) (truth : Fin m → Rat)
    (delta : Rat) (i : Fin m)
    -- Counts follow the stated conditional-binomial model.
    (sampling : BinomialSampling law truth)
    -- The row's true probability is nonnegative.
    (hp : 0 ≤ truth i)
    -- The row's true probability is at most one.
    (hp1 : truth i ≤ 1)
    -- The permitted error is nonnegative.
    (hd : 0 ≤ delta) :
    intervalMissProbability law truth delta i ≤ delta := by
  unfold intervalMissProbability
  rw [sampling.marginals i (fun count =>
    if (confidenceInterval delta count.trials count.deaths).Contains (truth i) then 0 else 1)]
  have bound := expectation_monotone (sampling.sizes i) (sampling.sizesValid i).1
    (fun n => binomialExpectation (truth i) n (fun k =>
      if (confidenceInterval delta n k).Contains (truth i) then 0 else 1))
    (fun _ => delta) (fun n => intervalConfidence (truth i) delta n hp hp1 hd)
  rw [expectation_constant _ (sampling.sizesValid i)] at bound
  exact bound

/-- Risk of accepting all rows when at least one true expectation violates its policy band. -/
def familyFalseAcceptance (law : Distribution (Fin m → Observation)) (truth : Fin m → Rat)
    (bands : Fin m → Band) (delta : Rat) : Rat :=
  expectation law fun counts =>
    if acceptsFamily bands delta counts ∧ ¬ familyBalanced truth bands then 1 else 0

/-- Requiring all rows to pass bounds the whole decision's false-acceptance risk by delta. -/
theorem familyFalseAcceptance_bound
    (law : Distribution (Fin m → Observation)) (truth : Fin m → Rat) (bands : Fin m → Band)
    (delta : Rat)
    -- The joint observation law is a probability distribution.
    (valid : law.Valid)
    -- Each row follows its conditional-binomial model.
    (sampling : BinomialSampling law truth)
    -- All true row probabilities lie in the unit interval.
    (probabilities : ∀ i, 0 ≤ truth i ∧ truth i ≤ 1)
    -- The permitted error is nonnegative.
    (hd : 0 ≤ delta) :
    familyFalseAcceptance law truth bands delta ≤ delta := by
  by_cases balanced : familyBalanced truth bands
  -- If every true probability fits, false acceptance is impossible.
  · have bound : familyFalseAcceptance law truth bands delta ≤ expectation law (fun _ => 0) := by
      apply expectation_monotone law valid.1
      intro counts
      simp only [balanced, not_true_eq_false, and_false, ite_false]
      exact Rat.le_refl
    rw [expectation_constant law valid] at bound
    exact Rat.le_trans bound hd
  -- Otherwise acceptance requires missing at least one fixed violating row.
  · obtain ⟨i, unbalanced⟩ := Classical.not_forall.mp balanced
    have bound : familyFalseAcceptance law truth bands delta ≤ intervalMissProbability law truth delta i := by
      apply expectation_monotone law valid.1
      intro counts
      split
      -- Passing every row implies this violating row was falsely accepted.
      · next accepted =>
        have missed := false_accept_misses (bands i) delta (truth i) (counts i) (accepted.1 i) unbalanced
        simp only [missed, ite_false]
        exact Rat.le_refl
      -- Rejected observations contribute no false-acceptance risk.
      · split <;> decide +kernel
    exact Rat.le_trans bound (rowConfidence law truth delta i sampling
      (probabilities i).1 (probabilities i).2 hd)

/-- The fixed confidence level is 95%; each interval has failure probability at most 5%. -/
def confidenceDelta : Rat := 1/20

/-- The configurable confidence level must remain strictly between zero and one. -/
theorem confidenceLevel_valid :
    -- A positive error allowance permits finite intervals.
    0 < confidenceDelta ∧
    -- The confidence guarantee is nontrivial.
    confidenceDelta < 1 := by decide +kernel

end Rpg.Probability.Confidence
