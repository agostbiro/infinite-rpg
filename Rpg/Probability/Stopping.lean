import Rpg.Probability.DistributionProofs

/-! Finite-horizon probabilities and almost-sure termination, stated without an
unverified infinite solver. A nonnegative potential decreases by at least one
expected unit on each unfinished step. This gives both a finite error bound and
probability-one termination in the rational epsilon formulation. -/
namespace Rpg.Probability

attribute [local simp] Rat.zero_add Rat.add_zero Rat.zero_mul Rat.mul_zero Rat.one_mul Rat.mul_one

structure StoppingProcess (α : Type) where
  step : α → Distribution α
  terminal : α → Bool
  valid : ∀ s, (step s).Valid

def StoppingProcess.unfinished (p : StoppingProcess α) : Nat → α → Rat
  | 0, s => if p.terminal s then 0 else 1
  | n+1, s => if p.terminal s then 0 else (p.step s).expect (p.unfinished n)

def StoppingProcess.duration (p : StoppingProcess α) : Nat → α → Rat
  | 0, _ => 0
  | n+1, s => if p.terminal s then 0 else 1 + (p.step s).expect (p.duration n)

theorem StoppingProcess.unfinished_bounds (p : StoppingProcess α) (n : Nat) (s : α) :
    0 ≤ p.unfinished n s ∧ p.unfinished n s ≤ 1 := by
  induction n generalizing s with
  | zero => simp only [unfinished]; split <;> decide
  | succ n ih =>
    simp only [unfinished]
    split
    · decide
    · constructor
      · have h := (p.step s).expect_mono (p.valid s) (fun _ => 0) (p.unfinished n)
          (fun e _ => (ih e.1).1)
        simpa [Distribution.expect_const _ (p.valid s)] using h
      · have h := (p.step s).expect_mono (p.valid s) (p.unfinished n) (fun _ => 1)
          (fun e _ => (ih e.1).2)
        simpa [Distribution.expect_const _ (p.valid s)] using h

variable {α : Type} {p : StoppingProcess α} {invariant : α → Prop}

/-- A local, independently checkable proof obligation, restricted to a closed set of states. -/
structure StoppingCertificate (p : StoppingProcess α) (invariant : α → Prop) where
  potential : α → Rat
  nonnegative : ∀ s, invariant s → 0 ≤ potential s
  closed : ∀ s, invariant s → ∀ e ∈ (p.step s).entries, invariant e.1
  decreases : ∀ s, invariant s → p.terminal s = false →
    1 + (p.step s).expect potential ≤ potential s

theorem StoppingCertificate.duration_le (c : StoppingCertificate p invariant)
    (n : Nat) (s : α) (hs : invariant s) : p.duration n s ≤ c.potential s := by
  induction n generalizing s with
  | zero => exact c.nonnegative s hs
  | succ n ih =>
    simp only [StoppingProcess.duration]
    split
    · exact c.nonnegative s hs
    · next ht =>
      have bound := (p.step s).expect_mono (p.valid s) (p.duration n) c.potential
        (fun e he => ih e.1 (c.closed s hs e he))
      have drift := c.decreases s hs (Bool.eq_false_iff.mpr ht)
      grind

theorem StoppingProcess.unfinished_mul_le_duration (p : StoppingProcess α) (n : Nat) (s : α) :
    (n : Rat) * p.unfinished n s ≤ p.duration n s := by
  induction n generalizing s with
  | zero => simp [duration]
  | succ n ih =>
    simp only [unfinished, duration]
    split
    · simp
    · have bound := (p.step s).expect_mono (p.valid s)
        (fun t => (n : Rat) * p.unfinished n t) (p.duration n) (fun e _ => ih e.1)
      have upper := (p.step s).expect_mono (p.valid s) (p.unfinished n) (fun _ => 1)
        (fun e _ => (p.unfinished_bounds n e.1).2)
      simp only [Distribution.expect, weightedSum_mul] at bound
      simp only [Distribution.expect_const _ (p.valid s)] at upper
      simp only [Rat.natCast_add]
      change ((n : Rat)+1) * (p.step s).expect (p.unfinished n) ≤ _
      change (n : Rat) * (p.step s).expect (p.unfinished n) ≤ (p.step s).expect (p.duration n) at bound
      grind

/-- Finite-horizon guarantee: choose enough rounds to make the remaining probability at most delta. -/
theorem StoppingCertificate.highProbability (c : StoppingCertificate p invariant)
    (s : α) (hs : invariant s) (n : Nat) (hn : 0 < n) (delta : Rat)
    (budget : c.potential s ≤ (n : Rat) * delta) : p.unfinished n s ≤ delta := by
  have h := Rat.le_trans (p.unfinished_mul_le_duration n s) (c.duration_le n s hs)
  exact Rat.le_of_mul_le_mul_left (Rat.le_trans h budget) (Rat.natCast_pos.mpr hn)

/-- Probability-one termination: every positive rational error has a finite horizon. -/
def StoppingProcess.AlmostSurelyTerminates (p : StoppingProcess α) (s : α) : Prop :=
  ∀ delta : Rat, 0 < delta → ∃ n : Nat, p.unfinished n s ≤ delta

/-- A concrete horizon for any requested error allowance. -/
def StoppingCertificate.horizon (c : StoppingCertificate p invariant) (s : α) (delta : Rat) : Nat :=
  (c.potential s / delta).ceil.toNat + 1

theorem StoppingCertificate.horizon_sound (c : StoppingCertificate p invariant)
    (s : α) (hs : invariant s) (delta : Rat) (hd : 0 < delta) :
    p.unfinished (c.horizon s delta) s ≤ delta := by
  let n := c.horizon s delta
  have ceiling : c.potential s / delta ≤ (((c.potential s / delta).ceil : Int) : Rat) := Rat.le_ceil
  have castBound : (((c.potential s / delta).ceil : Int) : Rat) ≤ (n : Rat) := by
    have hnat : (c.potential s / delta).ceil ≤ (n : Int) := by simp only [n, horizon]; omega
    exact Rat.intCast_le_intCast.mpr hnat
  have ratio := Rat.le_trans ceiling castBound
  have budget := Rat.mul_le_mul_of_nonneg_right ratio (Rat.le_of_lt hd)
  have nonzero : delta ≠ 0 := by grind
  have product : (c.potential s / delta) * delta = c.potential s := by grind
  rw [product] at budget
  exact c.highProbability s hs n (by simp [n,horizon]) delta budget

theorem StoppingCertificate.almostSure (c : StoppingCertificate p invariant)
    (s : α) (hs : invariant s) : p.AlmostSurelyTerminates s := by
  intro delta hd
  exact ⟨c.horizon s delta, c.horizon_sound s hs delta hd⟩

/-- Probability of an observed terminal event within n transitions. An unfinished
trajectory contributes zero, so its probability remains visible in `unfinished`. -/
def StoppingProcess.eventBy (p : StoppingProcess α) (event : α → Bool) : Nat → α → Rat
  | 0, s => if p.terminal s then (if event s then 1 else 0) else 0
  | n+1, s => if p.terminal s then (if event s then 1 else 0)
      else (p.step s).expect (p.eventBy event n)

/-- A candidate outcome value satisfies independently checked one-step equations. -/
structure OutcomeCertificate (p : StoppingProcess α) (invariant : α → Prop) (event : α → Bool) where
  value : α → Rat
  bounded : ∀ s, invariant s → 0 ≤ value s ∧ value s ≤ 1
  closed : ∀ s, invariant s → ∀ e ∈ (p.step s).entries, invariant e.1
  terminalValue : ∀ s, invariant s → p.terminal s = true → value s = (if event s then 1 else 0)
  equation : ∀ s, invariant s → p.terminal s = false → value s = (p.step s).expect value

/-- Every finite execution brackets the candidate value. Its entire uncertainty is
bounded by the probability of trajectories that have not finished yet. -/
theorem OutcomeCertificate.finite_error {event : α → Bool}
    (c : OutcomeCertificate p invariant event) (n : Nat) (s : α) (hs : invariant s) :
    p.eventBy event n s ≤ c.value s ∧ c.value s ≤ p.eventBy event n s + p.unfinished n s := by
  induction n generalizing s with
  | zero =>
    simp only [StoppingProcess.eventBy, StoppingProcess.unfinished]
    split
    · next ht => rw [c.terminalValue s hs ht]; simp
    · simpa using c.bounded s hs
  | succ n ih =>
    simp only [StoppingProcess.eventBy, StoppingProcess.unfinished]
    split
    · next ht => rw [c.terminalValue s hs ht]; simp
    · next ht =>
      rw [c.equation s hs (Bool.eq_false_iff.mpr ht)]
      constructor
      · exact (p.step s).expect_mono (p.valid s) _ _ (fun e he => (ih e.1 (c.closed s hs e he)).1)
      · have bound := (p.step s).expect_mono (p.valid s) c.value
          (fun t => p.eventBy event n t + p.unfinished n t)
          (fun e he => (ih e.1 (c.closed s hs e he)).2)
        simpa only [Distribution.expect, weightedSum_add] using bound

/-- Combining the two certificates gives an explicit error bound against actual
finite executions; it does not assume that the candidate solver is correct. -/
theorem OutcomeCertificate.highProbability_error {event : α → Bool}
    (c : OutcomeCertificate p invariant event) (stopping : StoppingCertificate p invariant)
    (s : α) (hs : invariant s) (delta : Rat) (hd : 0 < delta) :
    let n := stopping.horizon s delta
    p.eventBy event n s ≤ c.value s ∧ c.value s ≤ p.eventBy event n s + delta := by
  have finite := c.finite_error (stopping.horizon s delta) s hs
  have tail := stopping.horizon_sound s hs delta hd
  constructor
  · exact finite.1
  · have bound := finite.2; grind

end Rpg.Probability
