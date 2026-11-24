import MarkovRPG
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# Distribution-based fairness and conditional balance

A reference law is an actual `ProbabilityMeasure (WithTop ℕ)`. Finite values
represent defeat times; mass at infinity represents never losing. This also
allows a continuous reference law to be discretized at event timestamps.

Fairness compares the WHOLE cumulative curve with the reference CDF. Conditional
balance instead compares the full-history conditional expectation, on living
histories, with the reference residual risk at the same absolute timestamp.
Stability combines these two requirements. A separate check of h_2 against F(2)
at the initial vertex would be redundant with whole-curve fairness.

All bands are deterministic mathematical tolerances, not statistical confidence
intervals. No sampling or coverage claim is made. Tolerances are nonnegative
reals by type. No equality with the reference law is assumed about the game.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace MarkovRPG

/-- Absolute error is equivalent to membership in a two-sided band.
The order upper/lower agrees with the graph predicates in MarkovRPG.lean. -/
theorem abs_sub_le_iff_band (x center ε : ℝ) :
    |x - center| ≤ ε ↔ x ≤ center + ε ∧ center - ε ≤ x := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

namespace DefeatTime

variable (D : ProbabilityMeasure (WithTop ℕ))

/-- Reference cumulative defeat probability, including time zero. -/
def cdf (n : ℕ) : ℝ := (D : Measure (WithTop ℕ)).real (Iic (n : WithTop ℕ))

/-- Reference eventual defeat probability; mass at infinity is excluded. -/
def eventual : ℝ := (D : Measure (WithTop ℕ)).real (Iio ⊤)

theorem cdf_nonneg (n : ℕ) : 0 ≤ cdf D n := measureReal_nonneg

theorem cdf_le_one (n : ℕ) : cdf D n ≤ 1 := measureReal_le_one

theorem cdf_mono : Monotone (cdf D) := by
  intro n k hnk
  exact measureReal_mono (Iic_subset_Iic.mpr (by exact_mod_cast hnk)) (measure_ne_top _ _)

theorem cdf_le_eventual (n : ℕ) : cdf D n ≤ eventual D := by
  exact measureReal_mono (fun k hk ↦ hk.trans_lt (WithTop.coe_lt_top n)) (measure_ne_top _ _)

/-- Continuity from below also holds for the reference law. -/
theorem eventual_eq_iSup : eventual D = ⨆ n, cdf D n := by
  have heq : (Iio (⊤ : WithTop ℕ)) = ⋃ n : ℕ, Iic (n : WithTop ℕ) := by
    ext k
    simp only [mem_Iio, mem_iUnion, mem_Iic]
    constructor
    · intro hk
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hk)
      exact ⟨n, le_of_eq hn.symm⟩
    · rintro ⟨n, hn⟩
      exact hn.trans_lt (WithTop.coe_lt_top n)
  have hm : Monotone (fun n : ℕ ↦ Iic (n : WithTop ℕ)) := by
    intro n k hnk
    exact Iic_subset_Iic.mpr (by exact_mod_cast hnk)
  simp only [eventual, cdf, heq, measureReal_def, hm.measure_iUnion,
    ENNReal.toReal_iSup (fun _ ↦ measure_ne_top _ _)]

/-- Reference risk during (t,t+n], given survival beyond t. The explicit premise
prevents treating conditioning on a probability-zero survival event as meaningful. -/
def risk (t n : ℕ) (_ht : cdf D t < 1) : ℝ :=
  (cdf D (t + n) - cdf D t) / (1 - cdf D t)

theorem risk_nonneg (t n : ℕ) (ht : cdf D t < 1) : 0 ≤ risk D t n ht :=
  div_nonneg (sub_nonneg.mpr (cdf_mono D (Nat.le_add_right t n))) (by linarith)

theorem risk_le_one (t n : ℕ) (ht : cdf D t < 1) : risk D t n ht ≤ 1 := by
  unfold risk
  apply (div_le_one (by linarith : 0 < 1 - cdf D t)).mpr
  linarith [cdf_le_one D (t + n)]

/-- The CDF formula really is the ratio defining conditional probability. -/
theorem risk_eq_probability_ratio (t n : ℕ) (ht : cdf D t < 1) :
    risk D t n ht =
      (D : Measure (WithTop ℕ)).real (Iic ((t + n : ℕ) : WithTop ℕ) \ Iic (t : WithTop ℕ)) /
      (D : Measure (WithTop ℕ)).real (Iic (t : WithTop ℕ))ᶜ := by
  have hsub : Iic (t : WithTop ℕ) ⊆ Iic ((t + n : ℕ) : WithTop ℕ) :=
    Iic_subset_Iic.mpr (by exact_mod_cast Nat.le_add_right t n)
  rw [measureReal_sdiff hsub measurableSet_Iic, measureReal_compl measurableSet_Iic]
  simp [risk, cdf]

end DefeatTime

namespace MarkovChain

variable {V Label : Type*} [Fintype V] (M : MarkovChain V Label)

/-- Whole-curve fairness from a specified vertex, with a uniform tolerance. -/
def IsMarkovFairDistrib (s : V) (D : ProbabilityMeasure (WithTop ℕ)) (ε : ℝ≥0) : Prop :=
  ∀ n, |M.h n s - DefeatTime.cdf D n| ≤ (ε : ℝ)

/-- The explicitly requested upper and lower thresholds are F(n)+ε and F(n)-ε. -/
theorem isMarkovFairDistrib_iff_bands (s : V) (D : ProbabilityMeasure (WithTop ℕ)) (ε : ℝ≥0) :
    M.IsMarkovFairDistrib s D ε ↔
      ∀ n, M.h n s ≤ DefeatTime.cdf D n + ε ∧ DefeatTime.cdf D n - ε ≤ M.h n s := by
  simp only [IsMarkovFairDistrib, abs_sub_le_iff_band]

/-- Whole-curve fairness implies the corresponding eventual-risk band. -/
theorem IsMarkovFairDistrib.eventual_fair {s : V} {D : ProbabilityMeasure (WithTop ℕ)}
    {ε : ℝ≥0} (hf : M.IsMarkovFairDistrib s D ε) :
    M.IsMarkovpqFair s (DefeatTime.eventual D + ε) (DefeatTime.eventual D - ε) := by
  have hb := (M.isMarkovFairDistrib_iff_bands s D ε).mp hf
  constructor
  · apply ciSup_le
    intro n
    have hn := DefeatTime.cdf_le_eventual D n
    have hbn := (hb n).1
    linarith
  · have hsup : DefeatTime.eventual D ≤ M.hInf s + ε := by
      rw [DefeatTime.eventual_eq_iSup]
      apply ciSup_le
      intro n
      have hhn := M.h_le_hInf n s
      have hbn := (hb n).2
      linarith
    linarith

/-- Local graph test at absolute timestamp t, using the residual reference law. -/
def IsMarkovTwoStepBalancedDistrib (s : V) (D : ProbabilityMeasure (WithTop ℕ))
    (t : ℕ) (ht : DefeatTime.cdf D t < 1) (ε : ℝ≥0) : Prop :=
  M.IsMarkovTwoStepBalanced s (DefeatTime.risk D t 2 ht + ε) (DefeatTime.risk D t 2 ht - ε)

theorem isMarkovTwoStepBalancedDistrib_iff_abs (s : V) (D : ProbabilityMeasure (WithTop ℕ))
    (t : ℕ) (ht : DefeatTime.cdf D t < 1) (ε : ℝ≥0) :
    M.IsMarkovTwoStepBalancedDistrib s D t ht ε ↔
      |M.h 2 s - DefeatTime.risk D t 2 ht| ≤ (ε : ℝ) := by
  simp only [IsMarkovTwoStepBalancedDistrib, IsMarkovTwoStepBalanced, abs_sub_le_iff_band]

/-- At time zero, if the reference has no immediate defeats, its two-step band is
already implied by whole-curve fairness. This is why stability below quantifies
over living histories at every timestamp instead of duplicating this condition. -/
theorem IsMarkovFairDistrib.initial_twoStepBalanced {s : V}
    {D : ProbabilityMeasure (WithTop ℕ)} {ε : ℝ≥0}
    (hf : M.IsMarkovFairDistrib s D ε) (hzero : DefeatTime.cdf D 0 = 0) :
    M.IsMarkovTwoStepBalancedDistrib s D 0 (by rw [hzero]; norm_num) ε := by
  rw [M.isMarkovTwoStepBalancedDistrib_iff_abs]
  simpa [DefeatTime.risk, hzero] using hf 2

/-- Compatibility with the original statewise notion: whole-curve fairness gives
both the eventual band and the initial two-step band, without an extra premise. -/
theorem IsMarkovFairDistrib.statewise_stable {s : V}
    {D : ProbabilityMeasure (WithTop ℕ)} {ε : ℝ≥0} (hf : M.IsMarkovFairDistrib s D ε) :
    M.IsMarkovStable s (DefeatTime.eventual D + ε) (DefeatTime.eventual D - ε)
      (DefeatTime.cdf D 2 + ε) (DefeatTime.cdf D 2 - ε) :=
  ⟨hf.eventual_fair M, (M.isMarkovFairDistrib_iff_bands s D ε).mp hf 2⟩

section Realization
variable [MeasurableSpace V] [MeasurableSingletonClass V]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

namespace Realization
variable {M} (R : M.Realization (Ω := Ω))

/-- Distribution-based balance of the actual full-history conditional expectation.
The comparison is made only on histories that have survived through t. -/
def IsMarkovConditionalDistrib (D : ProbabilityMeasure (WithTop ℕ))
    (t : ℕ) (ht : DefeatTime.cdf D t < 1) (ε : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
    |R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω -
      DefeatTime.risk D t 2 ht| ≤ (ε : ℝ)

/-- Exact equivalence: the conditional-expectation requirement reduces to a local
two-step computation at the currently visited vertex, with the same tolerance. -/
theorem isMarkovConditionalDistrib_iff_current_balance (D : ProbabilityMeasure (WithTop ℕ))
    (t : ℕ) (ht : DefeatTime.cdf D t < 1) (ε : ℝ≥0) :
    R.IsMarkovConditionalDistrib D t ht ε ↔
      ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
        M.IsMarkovTwoStepBalancedDistrib (R.X t ω) D t ht ε := by
  simp only [IsMarkovConditionalDistrib, abs_sub_le_iff_band, IsMarkovTwoStepBalancedDistrib]
  exact R.conditional_band_iff_current_twoStepBalanced t _ _

/-- Distribution stability is initial whole-curve fairness AND conditional balance
after every living history at each timestamp for which the reference can survive.
Two tolerances allow independent global and local specifications; pass the same
epsilon twice when the intended bands have equal widths. -/
def IsMarkovStableDistrib (D : ProbabilityMeasure (WithTop ℕ)) (εglobal εlocal : ℝ≥0) : Prop :=
  M.IsMarkovFairDistrib M.initial D εglobal ∧
    ∀ (t : ℕ) (ht : DefeatTime.cdf D t < 1), R.IsMarkovConditionalDistrib D t ht εlocal

/-- A graph-local characterization of distribution stability; no new stochastic
assumption is hidden in the checker condition. -/
theorem isMarkovStableDistrib_iff (D : ProbabilityMeasure (WithTop ℕ)) (εglobal εlocal : ℝ≥0) :
    R.IsMarkovStableDistrib D εglobal εlocal ↔
      M.IsMarkovFairDistrib M.initial D εglobal ∧
        ∀ (t : ℕ) (ht : DefeatTime.cdf D t < 1),
          ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
            M.IsMarkovTwoStepBalancedDistrib (R.X t ω) D t ht εlocal := by
  simp only [IsMarkovStableDistrib, R.isMarkovConditionalDistrib_iff_current_balance]

/-- The distribution fairness predicate controls actual defeat probabilities. -/
theorem IsMarkovStableDistrib.probability_band {D : ProbabilityMeasure (WithTop ℕ)}
    {εglobal εlocal : ℝ≥0} (hs : R.IsMarkovStableDistrib D εglobal εlocal) (n : ℕ) :
    |R.μ.real {ω | M.tauL R.X ω ≤ (n : WithTop ℕ)} - DefeatTime.cdf D n| ≤ (εglobal : ℝ) := by
  rw [R.probability_tauL_le]
  exact hs.1 n

omit [MeasurableSingletonClass V] in
/-- Stability gives the requested two-sided conditional-expectation band. -/
theorem IsMarkovStableDistrib.conditional_band {D : ProbabilityMeasure (WithTop ℕ)}
    {εglobal εlocal : ℝ≥0} (hs : R.IsMarkovStableDistrib D εglobal εlocal)
    (t : ℕ) (ht : DefeatTime.cdf D t < 1) :
    ∀ᵐ ω ∂R.μ, ω ∈ M.alive R.X t →
      R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω ≤
        DefeatTime.risk D t 2 ht + εlocal ∧
      DefeatTime.risk D t 2 ht - εlocal ≤
        R.μ[(R.nextDefeat t 2).indicator (fun _ ↦ (1 : ℝ)) | R.F t] ω := by
  simpa only [IsMarkovConditionalDistrib, abs_sub_le_iff_band] using hs.2 t ht

end Realization
end Realization
end MarkovChain
end MarkovRPG
