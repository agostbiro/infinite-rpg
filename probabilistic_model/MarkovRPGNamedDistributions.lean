import MarkovRPGCombatEvents
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Reference distributions for RPG graphs

Bernoulli describes an outcome; discrete phase-type and discretized Weibull
describe a hitting time. The named graph properties below specialize the existing
fairness predicates. Epsilon is a deterministic tolerance, not a confidence level.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace MarkovRPG
namespace ReferenceLaw

/- A common construction avoids duplicating normalization and CDF proofs for the
two time distributions. An atom at zero is allowed; infinity has zero mass. -/
private def increment (F : ℕ → ℝ) : ℕ → ℝ
  | 0 => F 0
  | n + 1 => F (n + 1) - F n

private theorem increment_nonneg (F : ℕ → ℝ) (h0 : 0 ≤ F 0) (hm : Monotone F)
    (n : ℕ) : 0 ≤ increment F n := by
  cases n with
  | zero => exact h0
  | succ n => exact sub_nonneg.mpr (hm (Nat.le_succ n))

private theorem sum_increment (F : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), increment F i = F n := by
  induction n with
  | zero => simp [increment]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp [increment]

private def cdfPMF (F : ℕ → ℝ) (h0 : 0 ≤ F 0) (hm : Monotone F)
    (hlim : Tendsto F atTop (𝓝 1)) : PMF ℕ := by
  refine ⟨fun n => ENNReal.ofReal (increment F n), ?_⟩
  apply (ENNReal.hasSum_iff_tendsto_nat 1).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  have heq (n : ℕ) : (∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (increment F i)) =
      ENNReal.ofReal (F n) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => increment_nonneg F h0 hm i),
      sum_increment]
  simpa only [heq, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hlim

private def lawOfCDF (F : ℕ → ℝ) (h0 : 0 ≤ F 0) (hm : Monotone F)
    (hlim : Tendsto F atTop (𝓝 1)) : ProbabilityMeasure (WithTop ℕ) :=
  ⟨(PMF.map (fun n : ℕ => (n : WithTop ℕ)) (cdfPMF F h0 hm hlim)).toMeasure, inferInstance⟩

private theorem lawOfCDF_cdf (F : ℕ → ℝ) (h0 : 0 ≤ F 0) (hm : Monotone F)
    (hlim : Tendsto F atTop (𝓝 1)) (n : ℕ) :
    DefeatTime.cdf (lawOfCDF F h0 hm hlim) n = F n := by
  change ((PMF.map (fun k : ℕ => (k : WithTop ℕ)) (cdfPMF F h0 hm hlim)).toMeasure
    (Iic (n : WithTop ℕ))).toReal = F n
  rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) measurableSet_Iic]
  have hset : (fun k : ℕ => (k : WithTop ℕ)) ⁻¹' Iic (n : WithTop ℕ) =
      (Finset.range (n + 1) : Set ℕ) := by
    ext k
    simp
  rw [hset, PMF.toMeasure_apply_finset]
  change (∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (increment F i)).toReal = F n
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => increment_nonneg F h0 hm i),
    sum_increment, ENNReal.toReal_ofReal (h0.trans (hm (Nat.zero_le n)))]

private theorem lawOfCDF_eventual (F : ℕ → ℝ) (h0 : 0 ≤ F 0) (hm : Monotone F)
    (hlim : Tendsto F atTop (𝓝 1)) :
    DefeatTime.eventual (lawOfCDF F h0 hm hlim) = 1 := by
  change ((PMF.map (fun k : ℕ => (k : WithTop ℕ)) (cdfPMF F h0 hm hlim)).toMeasure
    (Iio (⊤ : WithTop ℕ))).toReal = 1
  rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) measurableSet_Iio]
  have hset : (fun k : ℕ => (k : WithTop ℕ)) ⁻¹' Iio (⊤ : WithTop ℕ) = univ := by
    ext k
    simp
  simp [hset]

/-! ## Bernoulli outcome -/

/-- The Boolean outcome law: true means Lose, with probability p; false means
Win only when the combat is known to terminate almost surely. -/
def bernoulli (p : Set.Icc (0 : ℝ) 1) : ProbabilityMeasure Bool :=
  ⟨bernoulliMeasure true false p, inferInstance⟩

@[simp] theorem bernoulli_lose (p : Set.Icc (0 : ℝ) 1) :
    (bernoulli p : Measure Bool).real {true} = (p : ℝ) := by
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton true)
    (by simp) (by simp)

@[simp] theorem bernoulli_win (p : Set.Icc (0 : ℝ) 1) :
    (bernoulli p : Measure Bool).real {false} = 1 - (p : ℝ) := by
  exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton false)
    (by simp) (by simp)

/-! ## Discrete phase-type hitting time -/

/-- A finite Markov reference with almost-sure absorption from the supplied
initial vertex. Its target set is `chain.defeat`; for combat duration it is the
union of Win and Lose. Stopping on the first target visit gives the usual
discrete phase-type distribution. No condition on unreachable states is needed.
This constructor uses a fixed initial phase, matching the graph API. -/
structure PhaseType (V Label : Type*) [Fintype V] where
  chain : MarkovChain V Label
  terminates : chain.hInf chain.initial = 1

namespace PhaseType
variable {V Label : Type*} [Fintype V] (d : PhaseType V Label)

/-- Exact first-hitting-time law, using the already proved Markov recurrence. -/
def law : ProbabilityMeasure (WithTop ℕ) :=
  lawOfCDF (fun n => d.chain.h n d.chain.initial)
    (d.chain.h_nonneg 0 _) (d.chain.h_mono _)
    (by
      have h := tendsto_atTop_ciSup (d.chain.h_mono d.chain.initial) (d.chain.h_bddAbove _)
      change Tendsto _ atTop (𝓝 (d.chain.hInf d.chain.initial)) at h
      rwa [d.terminates] at h)

@[simp] theorem cdf_law (n : ℕ) :
    DefeatTime.cdf d.law n = d.chain.h n d.chain.initial :=
  lawOfCDF_cdf _ _ _ _ n

@[simp] theorem eventual_law : DefeatTime.eventual d.law = 1 :=
  lawOfCDF_eventual _ _ _ _

end PhaseType

/-! ## Discretized Weibull hitting time -/

/-- Positive real scale and shape. Time is counted in graph transitions.
The discretization has survival P(T > n) = exp (-(n / scale)^shape), so T >= 1. -/
structure Weibull where
  scale : ℝ
  shape : ℝ
  scale_pos : 0 < scale
  shape_pos : 0 < shape

namespace Weibull
variable (d : Weibull)

def survival (n : ℕ) : ℝ := Real.exp (-(((n : ℝ) / d.scale) ^ d.shape))
def cdf (n : ℕ) : ℝ := 1 - d.survival n

@[simp] theorem cdf_zero : d.cdf 0 = 0 := by
  simp [cdf, survival, Real.zero_rpow (ne_of_gt d.shape_pos)]

theorem cdf_mono : Monotone d.cdf := by
  intro n m hnm
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact Real.rpow_le_rpow (div_nonneg (by positivity) d.scale_pos.le)
    (div_le_div_of_nonneg_right (by exact_mod_cast hnm) d.scale_pos.le) d.shape_pos.le

theorem cdf_tendsto : Tendsto d.cdf atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) / d.scale) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const d.scale_pos
  have hpow := (tendsto_rpow_atTop d.shape_pos).comp hbase
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  change Tendsto (fun n : ℕ => 1 - Real.exp (-(((n : ℝ) / d.scale) ^ d.shape))) atTop (𝓝 1)
  simpa only [sub_zero, Function.comp_apply] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hexp

/-- A normalized probability measure, constructed from the Weibull CDF. -/
def law : ProbabilityMeasure (WithTop ℕ) :=
  lawOfCDF d.cdf (by rw [d.cdf_zero]) d.cdf_mono d.cdf_tendsto

@[simp] theorem cdf_law (n : ℕ) :
    DefeatTime.cdf d.law n = 1 - Real.exp (-(((n : ℝ) / d.scale) ^ d.shape)) :=
  lawOfCDF_cdf _ _ _ _ n

@[simp] theorem eventual_law : DefeatTime.eventual d.law = 1 :=
  lawOfCDF_eventual _ _ _ _

end Weibull
end ReferenceLaw

namespace MarkovChain
variable {V Label : Type*} [Fintype V] (M : MarkovChain V Label)

/-- Specialization of eventual fairness to the Bernoulli indicator of defeat.
This is an outcome property, not a requirement on the time of defeat. The
complement means "never defeated"; identifying it with Win also needs almost-
sure termination, as required by `Combat.Event` below. -/
def IsMarkovFairBernoulli (s : V) (p : Set.Icc (0 : ℝ) 1) (ε : ℝ≥0) : Prop :=
  M.IsMarkovpqFair s ((p : ℝ) + ε) ((p : ℝ) - ε)

theorem isMarkovFairBernoulli_iff (s : V) (p : Set.Icc (0 : ℝ) 1) (ε : ℝ≥0) :
    M.IsMarkovFairBernoulli s p ε ↔
      |M.hInf s - (ReferenceLaw.bernoulli p : Measure Bool).real {true}| ≤ (ε : ℝ) := by
  rw [ReferenceLaw.bernoulli_lose, abs_sub_le_iff_band]
  rfl

/-- Application of whole-curve fairness to a finite absorbing reference chain.
For a combat duration check, the graph's target must be Win OR Lose. -/
def IsMarkovFairPhaseType {W Tag : Type*} [Fintype W] (s : V)
    (d : ReferenceLaw.PhaseType W Tag) (ε : ℝ≥0) : Prop :=
  M.IsMarkovFairDistrib s d.law ε

theorem isMarkovFairPhaseType_iff {W Tag : Type*} [Fintype W] (s : V)
    (d : ReferenceLaw.PhaseType W Tag) (ε : ℝ≥0) :
    M.IsMarkovFairPhaseType s d ε ↔
      ∀ n, |M.h n s - d.chain.h n d.chain.initial| ≤ (ε : ℝ) := by
  simp only [IsMarkovFairPhaseType, IsMarkovFairDistrib, ReferenceLaw.PhaseType.cdf_law]

/-- Application of whole-curve fairness to the discretized Weibull law.
It retains the existing additive tolerance F(n) ± epsilon at every n. -/
def IsMarkovFairWeibull (s : V) (d : ReferenceLaw.Weibull) (ε : ℝ≥0) : Prop :=
  M.IsMarkovFairDistrib s d.law ε

theorem isMarkovFairWeibull_iff (s : V) (d : ReferenceLaw.Weibull) (ε : ℝ≥0) :
    M.IsMarkovFairWeibull s d ε ↔ ∀ n,
      |M.h n s - (1 - Real.exp (-(((n : ℝ) / d.scale) ^ d.shape)))| ≤ (ε : ℝ) := by
  simp only [IsMarkovFairWeibull, IsMarkovFairDistrib, ReferenceLaw.Weibull.cdf_law]

/- Conditional balance and stability already take a probability measure: use
`d.law` with `IsMarkovTwoStepBalancedDistrib`, `IsMarkovConditionalDistrib`, or
`IsMarkovStableDistrib`. Their existing theorems apply without new definitions. -/

end MarkovChain

namespace Combat.Event
variable {r : Combat.Rules}

/-- Bernoulli acceptance for an actual terminating combat, reusing `IsFair`.
The parameter p is the desired loss probability, not the win probability. -/
def IsBernoulliFair (e : Combat.Event r) (p : Set.Icc (0 : ℝ) 1) (ε : ℝ≥0) : Prop :=
  e.IsFair ((p : ℝ) + ε) ((p : ℝ) - ε)

/-- The specialization really bounds the resolved combat outcome, including all
internal paths and the supplied characters' initial HP and statistics. -/
theorem isBernoulliFair_iff (e : Combat.Event r) (p : Set.Icc (0 : ℝ) 1) (ε : ℝ≥0) :
    e.IsBernoulliFair p ε ↔
      |(e.resolve.map Combat.FullExit.outcome .Lose).toReal - (p : ℝ)| ≤ (ε : ℝ) := by
  rw [IsBernoulliFair, e.fair_iff, abs_sub_le_iff_band]
  exact and_comm

end Combat.Event
end MarkovRPG
