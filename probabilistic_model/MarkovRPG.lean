import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic

/-!
# A fresh Markov-chain foundation for an RPG

This file is independent of the previous RPG implementation. Time is discrete and
states form a finite type. A state must contain all variables needed for the Markov
property (including health, inventory, and any relevant memory).

Edge weights are nonnegative real numbers and each row sums to one. Labels are
optional. Defeat states need not be absorbing: we track the FIRST visit to L.

`h n s` is cumulative defeat probability by time n, including time zero. `hInf s`
is its supremum. Eventual defeat means tau < infinity, NOT tau <= infinity.
Conditional-expectation results use mathlib's actual conditional expectation;
only the standard ONE-STEP Markov property is assumed about a realization.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Classical
attribute [local instance 10] Classical.propDecidable
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set

namespace MarkovRPG

/-- A finite labelled Markov chain, with an initial vertex and a set of defeats. -/
structure MarkovChain (V Label : Type*) [Fintype V] where
  initial : V
  label : V → Option Label
  transition : V → V → ℝ
  transition_nonneg : ∀ s v, 0 ≤ transition s v
  transition_sum : ∀ s, ∑ v, transition s v = 1
  defeat : Set V

variable {V Label : Type*} [Fintype V]

namespace MarkovChain

variable (M : MarkovChain V Label)

/-- Directed edges are exactly the transitions of positive probability. -/
def Edge (s v : V) : Prop := 0 < M.transition s v

/-- Applying the transition matrix to a state function. -/
def step (f : V → ℝ) (s : V) : ℝ := ∑ v, M.transition s v * f v

lemma step_nonneg {f : V → ℝ} (hf : ∀ v, 0 ≤ f v) (s : V) :
    0 ≤ M.step f s := Finset.sum_nonneg fun v _ ↦ mul_nonneg (M.transition_nonneg s v) (hf v)

lemma step_mono {f g : V → ℝ} (hfg : ∀ v, f v ≤ g v) (s : V) :
    M.step f s ≤ M.step g s :=
  Finset.sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left (hfg v) (M.transition_nonneg s v)

@[simp] lemma step_one (s : V) : M.step (fun _ ↦ 1) s = 1 := by
  simp [step, M.transition_sum]

/-- Finite-horizon cumulative risk; its probability interpretation is proved below. -/
def h : ℕ → V → ℝ
  | 0, s => if s ∈ M.defeat then 1 else 0
  | n + 1, s => if s ∈ M.defeat then 1 else M.step (h n) s

@[simp] theorem h_zero (s : V) : M.h 0 s = if s ∈ M.defeat then 1 else 0 := rfl

/-- First-step recurrence, including the boundary condition on defeat vertices. -/
theorem h_succ (n : ℕ) (s : V) :
    M.h (n + 1) s = if s ∈ M.defeat then 1 else ∑ v, M.transition s v * M.h n v := rfl

@[simp] theorem h_of_mem (n : ℕ) {s : V} (hs : s ∈ M.defeat) : M.h n s = 1 := by
  cases n <;> simp [h, hs]

theorem h_nonneg (n : ℕ) (s : V) : 0 ≤ M.h n s := by
  induction n generalizing s with
  | zero => simp only [h]; split <;> norm_num
  | succ n ih =>
    simp only [h]; split
    · norm_num
    · exact M.step_nonneg ih s

theorem h_le_one (n : ℕ) (s : V) : M.h n s ≤ 1 := by
  induction n generalizing s with
  | zero => simp only [h]; split <;> norm_num
  | succ n ih =>
    simp only [h]; split
    · exact le_rfl
    · simpa using M.step_mono ih s

/-- Cumulative risk increases with the observation horizon. -/
theorem h_mono (s : V) : Monotone (fun n ↦ M.h n s) := by
  have aux : ∀ n s, M.h n s ≤ M.h (n + 1) s := by
    intro k
    induction k with
    | zero =>
      intro v
      by_cases hv : v ∈ M.defeat
      · simp [h, hv]
      · simp only [h, if_neg hv]
        exact M.step_nonneg (M.h_nonneg 0) v
    | succ k ih =>
      intro v
      by_cases hv : v ∈ M.defeat
      · simp [h, hv]
      · simpa only [h, if_neg hv] using M.step_mono ih v
  exact monotone_nat_of_le_succ (fun n ↦ aux n s)

/-- Restarting at another vertex changes no transition or defeat rule. -/
def withInitial (s : V) : MarkovChain V Label := { M with initial := s }

@[simp] theorem withInitial_h (s v : V) (n : ℕ) : (M.withInitial s).h n v = M.h n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [h_succ, h_succ]
    change (if v ∈ M.defeat then 1 else ∑ w, M.transition v w * (M.withInitial s).h n w) = _
    simp only [ih]


/-- The supremum of finite-horizon risks. -/
def hInf (s : V) : ℝ := ⨆ n : ℕ, M.h n s

lemma h_bddAbove (s : V) : BddAbove (Set.range (fun n ↦ M.h n s)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact M.h_le_one n s⟩

theorem h_le_hInf (n : ℕ) (s : V) : M.h n s ≤ M.hInf s :=
  le_ciSup (M.h_bddAbove s) n

theorem hInf_le_one (s : V) : M.hInf s ≤ 1 := ciSup_le (M.h_le_one · s)

theorem hInf_nonneg (s : V) : 0 ≤ M.hInf s :=
  (M.h_nonneg 0 s).trans (M.h_le_hInf 0 s)

/-- Eventual-risk fairness from s. The user's parameter order is upper p, lower q.
Bounds outside [0,1] are allowed: they express a vacuous side of a tolerance band. -/
def IsMarkovpqFair (s : V) (p q : ℝ) : Prop := M.hInf s ≤ p ∧ q ≤ M.hInf s

/-- Two-step balance from s, independently of the eventual defeat probability. -/
def IsMarkovTwoStepBalanced (s : V) (p q : ℝ) : Prop := M.h 2 s ≤ p ∧ q ≤ M.h 2 s

/-- Stability combines eventual fairness and local two-step balance. -/
def IsMarkovStable (s : V) (p₁ q₁ p₂ q₂ : ℝ) : Prop :=
  M.IsMarkovpqFair s p₁ q₁ ∧ M.IsMarkovTwoStepBalanced s p₂ q₂

theorem IsMarkovpqFair.h_le {s : V} {p q : ℝ} (hf : M.IsMarkovpqFair s p q) (n : ℕ) :
    M.h n s ≤ p := (M.h_le_hInf n s).trans hf.1

/-- An eventual lower bound does NOT hold at every finite horizon. Every strictly
smaller threshold is nevertheless exceeded at some finite horizon. -/
theorem IsMarkovpqFair.exists_h_gt {s : V} {p q r : ℝ}
    (hf : M.IsMarkovpqFair s p q) (hr : r < q) : ∃ n, r < M.h n s := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (ciSup_le hn)) (hr.trans_le hf.2)

/-- Once reached, an approximate eventual lower bound holds at all later times. -/
theorem IsMarkovpqFair.eventually_h_ge {s : V} {p q ε : ℝ}
    (hf : M.IsMarkovpqFair s p q) (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → q - ε ≤ M.h n s := by
  obtain ⟨N, hN⟩ := hf.exists_h_gt M (show q - ε < q by linarith)
  exact ⟨N, fun n hn ↦ hN.le.trans (M.h_mono s hn)⟩

/-- First hitting time of L, with infinity for a path that never reaches L. -/
def tauL {Ω : Type*} (X : ℕ → Ω → V) : Ω → WithTop ℕ :=
  hittingAfter X M.defeat 0

theorem tauL_le_iff {Ω : Type*} (X : ℕ → Ω → V) (n : ℕ) (ω : Ω) :
    M.tauL X ω ≤ n ↔ ∃ k ≤ n, X k ω ∈ M.defeat := by
  unfold tauL
  simpa only [Set.mem_Icc, Nat.zero_le, true_and, Nat.cast_withTop] using
    (hittingAfter_le_iff (u := X) (s := M.defeat) (n := 0) (i := n) (ω := ω))

/-- A local hitting event, counted from t through t+n, with both endpoints. -/
def hitWindow {Ω : Type*} (X : ℕ → Ω → V) (t n : ℕ) : Set Ω :=
  {ω | ∃ k ≤ n, X (t + k) ω ∈ M.defeat}

/-- Histories on which the player is still alive at time t. -/
def alive {Ω : Type*} (X : ℕ → Ω → V) (t : ℕ) : Set Ω :=
  {ω | ∀ k ≤ t, X k ω ∉ M.defeat}

section Realization

variable [MeasurableSpace V] [MeasurableSingletonClass V]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A stochastic realization of the graph. F records the information available at
 time t. The Markov identity is required only for ONE transition. In particular,
 no hitting-time probability or fairness conclusion is assumed here. -/
structure Realization where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  F : Filtration ℕ mΩ
  X : ℕ → Ω → V
  adapted : ∀ t, Measurable[F t] (X t)
  starts : ∀ᵐ ω ∂μ, X 0 ω = M.initial
  markov : ∀ (t : ℕ) (f : V → ℝ),
    μ[(fun ω ↦ f (X (t + 1) ω)) | F t] =ᵐ[μ]
      fun ω ↦ M.step f (X t ω)

namespace Realization

variable {M} (R : M.Realization (Ω := Ω))

instance : IsProbabilityMeasure R.μ := R.probability

omit [MeasurableSingletonClass V] in
lemma measurable_X (t : ℕ) : Measurable (R.X t) :=
  (R.adapted t).mono (R.F.le t) le_rfl

lemma defeat_measurable (t : ℕ) : MeasurableSet[R.F t] {ω | R.X t ω ∈ M.defeat} :=
  (R.adapted t) (Set.toFinite M.defeat).measurableSet

lemma window_measurable (t n : ℕ) : MeasurableSet (M.hitWindow R.X t n) := by
  simp only [hitWindow, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : k ≤ n
  · simpa only [hk, true_and, Set.preimage] using
      (R.measurable_X (t + k) (Set.toFinite M.defeat).measurableSet)
  · simp [hk]

lemma window_integrable (t n : ℕ) :
    Integrable ((M.hitWindow R.X t n).indicator (fun _ ↦ (1 : ℝ))) R.μ :=
  (integrable_const 1).indicator (R.window_measurable t n)

/-- The first hitting time is a stopping time for the history filtration. -/
theorem tauL_isStoppingTime : IsStoppingTime R.F (M.tauL R.X) :=
  Adapted.isStoppingTime_hittingAfter R.adapted (Set.toFinite M.defeat).measurableSet

lemma alive_measurable (t : ℕ) : MeasurableSet[R.F t] (M.alive R.X t) := by
  have heq : M.alive R.X t = {ω | M.tauL R.X ω ≤ (t : WithTop ℕ)}ᶜ := by
    ext ω
    simp [alive, M.tauL_le_iff]
  rw [heq]
  exact (R.tauL_isStoppingTime.measurableSet_le t).compl

omit [MeasurableSingletonClass V] in
lemma window_zero (t : ℕ) : M.hitWindow R.X t 0 = {ω | R.X t ω ∈ M.defeat} := by
  ext ω
  simp [hitWindow]

omit [MeasurableSingletonClass V] in
lemma window_succ (t n : ℕ) :
    M.hitWindow R.X t (n + 1) =
      {ω | R.X t ω ∈ M.defeat} ∪ M.hitWindow R.X (t + 1) n := by
  ext ω
  constructor
  · rintro ⟨k, hk, hx⟩
    cases k with
    | zero => exact Or.inl (by simpa using hx)
    | succ k => exact Or.inr ⟨k, Nat.le_of_succ_le_succ hk, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx⟩
  · rintro (hx | ⟨k, hk, hx⟩)
    · exact ⟨0, Nat.zero_le _, by simpa using hx⟩
    · exact ⟨k + 1, Nat.succ_le_succ hk, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx⟩

/-- Markov first-step analysis at an arbitrary time, conditioned on the entire
 history. This is proved by induction using the tower and pull-out properties. -/
theorem condExp_hitWindow (t n : ℕ) :
    R.μ[((M.hitWindow R.X t n).indicator (fun _ ↦ (1 : ℝ))) | R.F t] =ᵐ[R.μ]
      fun ω ↦ M.h n (R.X t ω) := by
  induction n generalizing t with
  | zero =>
    rw [R.window_zero]
    rw [condExp_of_stronglyMeasurable (R.F.le t)
      (stronglyMeasurable_const.indicator (R.defeat_measurable t))
      ((integrable_const 1).indicator (R.F.le t _ (R.defeat_measurable t)))]
    exact Filter.Eventually.of_forall fun ω ↦ by simp [h, Set.indicator_apply]
  | succ n ih =>
    let D : Set Ω := {ω | R.X t ω ∈ M.defeat}
    let g : Ω → ℝ := (M.hitWindow R.X (t + 1) n).indicator (fun _ ↦ 1)
    have hD : MeasurableSet[R.F t] D := R.defeat_measurable t
    have hg : Integrable g R.μ := R.window_integrable (t + 1) n
    have decomp : (M.hitWindow R.X t (n + 1)).indicator (fun _ ↦ (1 : ℝ)) =
        D.indicator (fun _ ↦ 1) + Dᶜ.indicator g := by
      rw [R.window_succ]
      ext ω
      by_cases hd : ω ∈ D <;> by_cases hf : ω ∈ M.hitWindow R.X (t + 1) n <;>
        simp_all [D, g]
    have future : R.μ[g | R.F t] =ᵐ[R.μ]
        fun ω ↦ M.step (M.h n) (R.X t ω) := by
      calc
        R.μ[g | R.F t] =ᵐ[R.μ] R.μ[R.μ[g | R.F (t + 1)] | R.F t] :=
          (condExp_condExp_of_le (R.F.mono (Nat.le_succ t)) (R.F.le (t + 1))).symm
        _ =ᵐ[R.μ] R.μ[(fun ω ↦ M.h n (R.X (t + 1) ω)) | R.F t] :=
          condExp_congr_ae (ih (t + 1))
        _ =ᵐ[R.μ] fun ω ↦ M.step (M.h n) (R.X t ω) := R.markov t (M.h n)
    rw [decomp]
    have hadd := condExp_add
      ((integrable_const (1 : ℝ)).indicator (R.F.le t _ hD))
      (hg.indicator (R.F.le t _ hD.compl)) (R.F t)
    have hfirst : R.μ[D.indicator (fun _ ↦ (1 : ℝ)) | R.F t] =
        D.indicator (fun _ ↦ 1) :=
      condExp_of_stronglyMeasurable (R.F.le t)
        (stronglyMeasurable_const.indicator hD)
        ((integrable_const 1).indicator (R.F.le t _ hD))
    have hpull := condExp_indicator hg hD.compl
    filter_upwards [hadd, hpull, future] with ω ha hp hf
    rw [ha, Pi.add_apply, hfirst, hp]
    by_cases hd : ω ∈ D
    · have hx : R.X t ω ∈ M.defeat := hd
      simp only [Set.indicator_apply, Set.mem_compl_iff, hd, not_true_eq_false,
        if_true, if_false, add_zero, h, if_pos hx]
    · simp only [Set.indicator_apply, Set.mem_compl_iff, hd, not_false_eq_true,
        if_true, if_false, zero_add]
      have hx : R.X t ω ∉ M.defeat := hd
      simpa only [h, if_neg hx] using hf

/-- The recursively computed h_n really is Pr(tau_L <= n) from the initial state. -/
theorem probability_tauL_le (n : ℕ) :
    R.μ.real {ω | M.tauL R.X ω ≤ (n : WithTop ℕ)} = M.h n M.initial := by
  have event_eq : {ω | M.tauL R.X ω ≤ (n : WithTop ℕ)} = M.hitWindow R.X 0 n := by
    ext ω
    simp [M.tauL_le_iff, hitWindow]
  rw [event_eq]
  have integral_eq : (∫ ω, (M.hitWindow R.X 0 n).indicator
      (fun _ ↦ (1 : ℝ)) ω ∂R.μ) = R.μ.real (M.hitWindow R.X 0 n) := by
    simp [integral_indicator (R.window_measurable 0 n)]
  rw [← integral_eq]
  rw [← integral_condExp (μ := R.μ) (R.F.le 0) (f := (M.hitWindow R.X 0 n).indicator (fun _ ↦ (1 : ℝ)))]
  have heq := (R.condExp_hitWindow 0 n).trans
    (R.starts.mono fun ω hw ↦ congrArg (M.h n) hw)
  rw [integral_congr_ae heq]
  simp

/-- Continuity from below identifies the infinite-horizon risk with eventual defeat. -/
theorem probability_tauL_lt_top :
    R.μ.real {ω | M.tauL R.X ω < ⊤} = M.hInf M.initial := by
  have event_eq : {ω | M.tauL R.X ω < ⊤} =
      ⋃ n : ℕ, {ω | M.tauL R.X ω ≤ (n : WithTop ℕ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt ht)
      exact ⟨n, le_of_eq hn.symm⟩
    · rintro ⟨n, hn⟩
      exact hn.trans_lt (WithTop.coe_lt_top n)
  have mono : Monotone (fun n : ℕ ↦ {ω | M.tauL R.X ω ≤ (n : WithTop ℕ)}) := by
    intro n k hnk ω hw
    change M.tauL R.X ω ≤ (n : WithTop ℕ) at hw
    change M.tauL R.X ω ≤ (k : WithTop ℕ)
    exact le_trans hw (by exact_mod_cast hnk)
  rw [event_eq, measureReal_def, mono.measure_iUnion,
    ENNReal.toReal_iSup (fun _ ↦ measure_ne_top _ _)]
  exact congrArg iSup (funext fun n ↦ R.probability_tauL_le n)

/-- The event of a NEW defeat during the next n transitions. The strict lower
 endpoint excludes a defeat which has already happened at the observation time. -/
def nextDefeat (t n : ℕ) : Set Ω :=
  {ω | (t : WithTop ℕ) < M.tauL R.X ω ∧ M.tauL R.X ω ≤ ((t + n : ℕ) : WithTop ℕ)}

omit [MeasurableSingletonClass V] in
lemma nextDefeat_eq (t n : ℕ) :
    R.nextDefeat t n = M.alive R.X t ∩ M.hitWindow R.X t n := by
  ext ω
  simp only [nextDefeat, Set.mem_ofPred_eq, Set.mem_inter_iff, ← not_le,
    M.tauL_le_iff]
  constructor
  · rintro ⟨ha, k, hk, hx⟩
    have hkt : t ≤ k := by
      by_contra hkt
      exact ha ⟨k, by omega, hx⟩
    refine ⟨?_, k - t, by omega, ?_⟩
    · simpa only [alive, Set.mem_ofPred_eq, not_exists, not_and] using ha
    · simpa only [Nat.add_sub_of_le hkt] using hx
  · rintro ⟨ha, k, hk, hx⟩
    refine ⟨?_, t + k, by omega, hx⟩
    rintro ⟨j, hj, hxj⟩
    exact ha j hj hxj

/-- Exact conditional first-defeat identity, valid without absorbing defeat states.
 This is an equality almost surely, rather than a statistical estimate. -/
theorem condExp_nextDefeat (t n : ℕ) :
    R.μ[(R.nextDefeat t n).indicator (fun _ ↦ (1 : ℝ)) | R.F t] =ᵐ[R.μ]
      (M.alive R.X t).indicator (fun ω ↦ M.h n (R.X t ω)) := by
  rw [R.nextDefeat_eq]
  have hi : (M.alive R.X t ∩ M.hitWindow R.X t n).indicator (fun _ ↦ (1 : ℝ)) =
      (M.alive R.X t).indicator ((M.hitWindow R.X t n).indicator (fun _ ↦ 1)) := by
    ext ω
    by_cases ha : ω ∈ M.alive R.X t <;>
      by_cases hw : ω ∈ M.hitWindow R.X t n <;> simp [ha, hw]
  rw [hi]
  have hpull := condExp_indicator (R.window_integrable t n) (R.alive_measurable t)
  filter_upwards [hpull, R.condExp_hitWindow t n] with ω hp hh
  rw [hp]
  by_cases ha : ω ∈ M.alive R.X t <;> simp [ha, hh]

/-- The sharp local hypothesis: bound h_2 only on the living states encountered
 at this timestamp. It need not hold at unreachable or already-losing states. -/
theorem conditional_defeat_le_of_local_bound (t : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hlocal : ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t → M.h 2 (R.X t ω) ≤ q) :
    R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ≤ᵐ[R.μ]
      fun _ ↦ q := by
  filter_upwards [R.condExp_nextDefeat t 2, hlocal] with ω heq hbound
  rw [heq]
  by_cases ha : ω ∈ M.alive R.X t
  · simpa only [Set.indicator_of_mem ha] using hbound ha
  · simpa only [Set.indicator_of_notMem ha] using hq

/-- The local risk condition is also necessary: no stronger uniform bound on
unvisited states is needed for a guarantee at the current timestamp. -/
theorem conditional_bound_iff_current_risk (t : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ≤ᵐ[R.μ]
      fun _ ↦ q) ↔
    (∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t → M.h 2 (R.X t ω) ≤ q) := by
  constructor
  · intro hb
    filter_upwards [R.condExp_nextDefeat t 2, hb] with ω heq hbound
    intro ha
    simpa only [heq, Set.indicator_of_mem ha] using hbound
  · exact R.conditional_defeat_le_of_local_bound t hq

/-- A two-sided conditional band is equivalent to two-step balance at the current
living state. Restricting to living histories is essential for a positive lower
bound: after death the indicator of a NEW defeat is zero. -/
theorem conditional_band_iff_current_twoStepBalanced (t : ℕ) (p q : ℝ) :
    (∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
      R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω ≤ p ∧
      q ≤ R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω) ↔
    (∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t → M.IsMarkovTwoStepBalanced (R.X t ω) p q) := by
  constructor <;> intro hb <;>
    filter_upwards [R.condExp_nextDefeat t 2, hb] with ω heq hbound <;>
    intro ha <;>
    simpa only [heq, Set.indicator_of_mem ha, IsMarkovTwoStepBalanced] using hbound ha

/-- Stability is required where play currently is, not merely at the old start.
No additional fairness premise is needed for the conditional part of the proof. -/
theorem stable_conditional_defeat_band (t : ℕ) {p₁ q₁ p₂ q₂ : ℝ}
    (hlocal : ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
      M.IsMarkovStable (R.X t ω) p₁ q₁ p₂ q₂) :
    ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
      R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω ≤ p₂ ∧
      q₂ ≤ R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω :=
  (R.conditional_band_iff_current_twoStepBalanced t p₂ q₂).mpr
    (hlocal.mono fun _ hw ha ↦ (hw ha).2)

/-- A stronger, purely graph-based sufficient check on all non-defeat states. -/
theorem conditional_defeat_band_of_all_live_states (t : ℕ) {p q : ℝ}
    (hgraph : ∀ s, s ∉ M.defeat → M.IsMarkovTwoStepBalanced s p q) :
    ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
      R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω ≤ p ∧
      q ≤ R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω :=
  (R.conditional_band_iff_current_twoStepBalanced t p q).mpr
    (Filter.Eventually.of_forall fun ω ha ↦ hgraph (R.X t ω) (ha t le_rfl))

/-- Exact formula for the CLOSED window originally requested. The extra first
 term explains why its unconditional upper bound fails at tau=t when q<1. -/
theorem condExp_closedWindow (t : ℕ) :
    R.μ[({ω | (t : WithTop ℕ) ≤ M.tauL R.X ω ∧
      M.tauL R.X ω ≤ ((t + 2 : ℕ) : WithTop ℕ)}).indicator
        (fun _ ↦ (1 : ℝ)) | R.F t] =ᵐ[R.μ]
    fun ω ↦ ({ω | M.tauL R.X ω = (t : WithTop ℕ)}).indicator (fun _ ↦ (1 : ℝ)) ω +
      (M.alive R.X t).indicator (fun ω ↦ M.h 2 (R.X t ω)) ω := by
  let D : Set Ω := {ω | M.tauL R.X ω = (t : WithTop ℕ)}
  have hD : MeasurableSet[R.F t] D := by
    simpa only [D, Nat.cast_withTop] using
      R.tauL_isStoppingTime.measurableSet_eq_of_countable t
  have hnext : MeasurableSet (R.nextDefeat t 2) := by
    rw [R.nextDefeat_eq]
    exact (R.F.le t _ (R.alive_measurable t)).inter (R.window_measurable t 2)
  have decomp : ({ω | (t : WithTop ℕ) ≤ M.tauL R.X ω ∧
      M.tauL R.X ω ≤ ((t + 2 : ℕ) : WithTop ℕ)}).indicator (fun _ ↦ (1 : ℝ)) =
      D.indicator (fun _ ↦ 1) + (R.nextDefeat t 2).indicator (fun _ ↦ 1) := by
    ext ω
    by_cases hd : M.tauL R.X ω = (t : WithTop ℕ)
    · simp [D, nextDefeat, hd]
    · by_cases hlt : (t : WithTop ℕ) < M.tauL R.X ω
      · simp [Set.indicator_apply, D, nextDefeat, hd, hlt, hlt.le]
      · have hnle : ¬ (t : WithTop ℕ) ≤ M.tauL R.X ω := by
          intro hl
          exact hlt (lt_of_le_of_ne hl (Ne.symm hd))
        simp [D, nextDefeat, hd, hlt, hnle]
  rw [decomp]
  have hadd := condExp_add (μ := R.μ) ((integrable_const (1 : ℝ)).indicator (R.F.le t _ hD))
    ((integrable_const (1 : ℝ)).indicator hnext) (R.F t)
  have hknown : R.μ[D.indicator (fun _ ↦ (1 : ℝ)) | R.F t] = D.indicator (fun _ ↦ 1) :=
    condExp_of_stronglyMeasurable (R.F.le t) (stronglyMeasurable_const.indicator hD)
      ((integrable_const 1).indicator (R.F.le t _ hD))
  filter_upwards [hadd, R.condExp_nextDefeat t 2] with ω ha hf
  simpa only [Pi.add_apply, hknown, hf] using ha

/-- The closed-window band is valid while the player is still alive. -/
theorem closedWindow_band_while_alive {p q : ℝ} (t : ℕ)
    (hlocal : ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t → M.IsMarkovTwoStepBalanced (R.X t ω) p q) :
    ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
      R.μ[({ω | (t : WithTop ℕ) ≤ M.tauL R.X ω ∧
        M.tauL R.X ω ≤ ((t + 2 : ℕ) : WithTop ℕ)}).indicator
          (fun _ ↦ (1 : ℝ)) | R.F t] ω ≤ p ∧
      q ≤ R.μ[({ω | (t : WithTop ℕ) ≤ M.tauL R.X ω ∧
        M.tauL R.X ω ≤ ((t + 2 : ℕ) : WithTop ℕ)}).indicator
          (fun _ ↦ (1 : ℝ)) | R.F t] ω := by
  filter_upwards [R.condExp_closedWindow t, hlocal] with ω heq hbound
  intro ha
  have hn : ¬ M.tauL R.X ω ≤ (t : WithTop ℕ) := by
    rw [M.tauL_le_iff]
    rintro ⟨k, hk, hx⟩
    exact ha k hk hx
  have hne : M.tauL R.X ω ≠ (t : WithTop ℕ) := fun he ↦ hn (le_of_eq he)
  rw [heq]
  simpa [Set.indicator_apply, hne, ha, IsMarkovTwoStepBalanced] using hbound ha

end Realization
end Realization

end MarkovChain

/-! ## A checked counterexample to extrapolating initial stability

Vertices: 0 = start, 1 = trap, 2 = defeat, 3 = safe. From the start, the trap
and the safe vertex each have probability 1/2. The trap then loses surely.
The initial state has both risks exactly 1/2, but a positive-probability living successor
has two-step risk 1. Thus initial stability alone is not a conditional guarantee.
-/
namespace Counterexample

/-- A four-state graph witnessing the missing local hypothesis. -/
def chain : MarkovChain (Fin 4) Unit where
  initial := 0
  label := fun _ ↦ none
  transition := fun s v ↦
    if s.val = 0 then (if v.val = 1 ∨ v.val = 3 then 1 / 2 else 0)
    else if s.val = 1 then (if v.val = 2 then 1 else 0)
    else if v.val = s.val then 1 else 0
  transition_nonneg := by intro s v; split_ifs <;> norm_num
  transition_sum := by
    intro s
    rw [Fin.sum_univ_four]
    fin_cases s <;> norm_num
  defeat := {s | s.val = 2}

lemma safe_risk_zero (n : ℕ) : chain.h n 3 = 0 := by
  induction n with
  | zero => norm_num [MarkovChain.h, chain]
  | succ n ih =>
    simpa [MarkovChain.h, MarkovChain.step, chain, Fin.sum_univ_four] using ih

lemma initial_risk_le_half (n : ℕ) : chain.h n 0 ≤ (1 / 2 : ℝ) := by
  cases n with
  | zero => norm_num [MarkovChain.h, chain]
  | succ n =>
    have hbound := chain.h_le_one n 1
    have heq : chain.h (n + 1) 0 = (1 / 2 : ℝ) * chain.h n 1 := by
      rw [chain.h_succ]
      norm_num [chain, Fin.sum_univ_four]
      simpa [chain] using safe_risk_zero n
    rw [heq]
    linarith

lemma initial_two_step : chain.h 2 chain.initial = (1 / 2 : ℝ) := by
  norm_num [MarkovChain.h, MarkovChain.step, chain, Fin.sum_univ_four]

/-- Even zero-width bands at the initial state do not control successor risks. -/
theorem initial_stable : chain.IsMarkovStable chain.initial (1 / 2) (1 / 2) (1 / 2) (1 / 2) := by
  refine ⟨⟨ciSup_le initial_risk_le_half, ?_⟩, ?_⟩
  · rw [← initial_two_step]
    exact chain.h_le_hInf 2 chain.initial
  · simp [MarkovChain.IsMarkovTwoStepBalanced, initial_two_step]

/-- A lower bound on eventual risk cannot be transferred to every finite time. -/
theorem eventual_lower_bound_not_finite :
    chain.IsMarkovpqFair chain.initial (1 / 2) (1 / 2) ∧ chain.h 0 chain.initial < 1 / 2 := by
  exact ⟨initial_stable.1, by norm_num [MarkovChain.h, chain]⟩

/-- The local risk can nevertheless be 1 immediately after a positive-probability edge. -/
theorem living_successor_violates_bound :
    chain.Edge chain.initial 1 ∧ (1 : Fin 4) ∉ chain.defeat ∧
      (1 / 2 : ℝ) < chain.h 2 1 := by
  norm_num [MarkovChain.Edge, MarkovChain.h, MarkovChain.step, chain, Fin.sum_univ_four]

end Counterexample

end MarkovRPG
