import MarkovRPGCombat
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Output probabilities and termination certificates

The proofs concern the combat kernel actually constructed in MarkovRPGCombat.
Win and Lose partition finite termination. Their probabilities sum to one when
termination is almost sure. No fairness, termination, or statistical confidence
claim is smuggled into the graph constructor.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace MarkovRPG.Combat
variable {r : Rules}

theorem Setup.chain_absorbing (c : Setup r) (policy : Policy c) (s : Vertex r)
    (o : Outcome) (hs : s.output = some o) (goal : Option Outcome) (next : Vertex r) :
    (c.chain policy goal).transition s next = if next = s then 1 else 0 := by
  by_cases heq : next = s <;>
    simp [chain, c.row_absorbing policy s o hs, PMF.pure_apply, heq]

theorem Setup.h_terminal (c : Setup r) (policy : Policy c) (s : Vertex r)
    (o : Outcome) (hs : s.output = some o) (goal : Option Outcome) (n : Nat) :
    (c.chain policy goal).h n s =
      if s ∈ (c.chain policy goal).defeat then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [MarkovChain.h_succ]
    split
    · rfl
    · simp [c.chain_absorbing policy s o hs, *]

/-- Finite-horizon termination consists exactly of the two disjoint outcomes. -/
theorem win_add_lose_by (c : Setup r) (policy : Policy c) (n : Nat) (s : Vertex r) :
    (c.chain policy (some .Win)).h n s + (c.chain policy (some .Lose)).h n s =
      (c.chain policy none).h n s := by
  induction n generalizing s with
  | zero =>
    cases hs : s.output with
    | none => simp [MarkovChain.h_zero, Setup.chain, hs]
    | some o => cases o <;> simp [MarkovChain.h_zero, Setup.chain, hs]
  | succ n ih =>
    cases hs : s.output with
    | some o =>
      simp only [c.h_terminal policy s o hs]
      cases o <;> simp [Setup.chain, hs]
    | none =>
      have hw : s ∉ (c.chain policy (some .Win)).defeat := by simp [Setup.chain, hs]
      have hl : s ∉ (c.chain policy (some .Lose)).defeat := by simp [Setup.chain, hs]
      have ht : s ∉ (c.chain policy none).defeat := by simp [Setup.chain, hs]
      simp only [MarkovChain.h_succ, if_neg hw, if_neg hl, if_neg ht]
      change (∑ v, (c.row policy s v).toReal * (c.chain policy (some .Win)).h n v) +
        (∑ v, (c.row policy s v).toReal * (c.chain policy (some .Lose)).h n v) = _
      rw [← Finset.sum_add_distrib]
      simp_rw [← mul_add, ih]
      rfl

/-- This identity also applies to combats which have positive probability of
never ending; the missing mass is exactly nontermination. -/
theorem win_add_lose (c : Setup r) (policy : Policy c) (s : Vertex r) :
    winProbability c policy s + loseProbability c policy s =
      terminationProbability c policy s := by
  change (⨆ n, (c.chain policy (some .Win)).h n s) +
    (⨆ n, (c.chain policy (some .Lose)).h n s) = ⨆ n, (c.chain policy none).h n s
  have hw := tendsto_atTop_ciSup ((c.chain policy (some .Win)).h_mono s)
    ((c.chain policy (some .Win)).h_bddAbove s)
  have hl := tendsto_atTop_ciSup ((c.chain policy (some .Lose)).h_mono s)
    ((c.chain policy (some .Lose)).h_bddAbove s)
  have ht := tendsto_atTop_ciSup ((c.chain policy none).h_mono s)
    ((c.chain policy none).h_bddAbove s)
  exact tendsto_nhds_unique (hw.add hl) (by simpa only [win_add_lose_by] using ht)

theorem IsTerminating.win_add_lose_eq_one {c : Setup r} {policy : Policy c}
    {s : Vertex r} (h : IsTerminating c policy s) :
    winProbability c policy s + loseProbability c policy s = 1 :=
  (win_add_lose c policy s).trans h

def conditionalWinProbability (c : Setup r) (policy : Policy c) (s : Vertex r)
    (_positive : 0 < terminationProbability c policy s) : ℝ :=
  winProbability c policy s / terminationProbability c policy s

theorem IsTerminating.conditional_win {c : Setup r} {policy : Policy c}
    {s : Vertex r} (h : IsTerminating c policy s) :
    conditionalWinProbability c policy s (by rw [h]; norm_num) = winProbability c policy s := by
  change terminationProbability c policy s = 1 at h
  simp [conditionalWinProbability, h]

/-- Acceptance from the supplied character snapshots: both fighters start
alive, termination is almost sure, and the loss probability lies in `[q, p]`.
`Setup` already checks the shared bounds on statistics, equipment, and effects.
The policy is explicit; acceptance under one policy does not quantify over all
strategies. The upper bound `p` precedes `q`, as in the existing fairness API.
No local two-event balance is required. -/
def IsValid (c : Setup r) (policy : Policy c) (p q : ℝ) : Prop :=
  c.initial.output = none ∧
    IsTerminating c policy c.initial ∧ IsFair c policy c.initial p q

theorem IsValid.initial_alive {c : Setup r} {policy : Policy c} {p q : ℝ}
    (h : IsValid c policy p q) (player : Player) :
    0 < (c.characters player).character.hp :=
  c.initial_alive_iff.mp h.1 player

theorem IsValid.lose_band {c : Setup r} {policy : Policy c} {p q : ℝ}
    (h : IsValid c policy p q) :
    q ≤ loseProbability c policy c.initial ∧
      loseProbability c policy c.initial ≤ p :=
  ⟨h.2.2.2, h.2.2.1⟩

/-- The graph contract is exactly the requested condition on the actual inputs
and output probabilities; no extra balance condition is hidden in it. -/
theorem isValid_iff_input_contract (c : Setup r) (policy : Policy c) (p q : ℝ) :
    IsValid c policy p q ↔
      (∀ player, 0 < (c.characters player).character.hp) ∧
      terminationProbability c policy c.initial = 1 ∧
      q ≤ loseProbability c policy c.initial ∧
      loseProbability c policy c.initial ≤ p := by
  constructor
  · intro h
    exact ⟨h.initial_alive, h.2.1, h.lose_band⟩
  · rintro ⟨alive, terminates, lower, upper⟩
    exact ⟨c.initial_alive_iff.mpr alive, terminates, upper, lower⟩

/-- A maximum acceptable risk is the special case with lower bound zero.
No second notion of fairness is needed. -/
theorem isValid_zero_lower_iff (c : Setup r) (policy : Policy c) (p : ℝ) :
    IsValid c policy p 0 ↔
      (∀ player, 0 < (c.characters player).character.hp) ∧
      terminationProbability c policy c.initial = 1 ∧
      loseProbability c policy c.initial ≤ p := by
  rw [isValid_iff_input_contract]
  have hnonneg : 0 ≤ loseProbability c policy c.initial :=
    (c.chain policy (some .Lose)).hInf_nonneg c.initial
  simp only [hnonneg, true_and]

theorem IsValid.win_band {c : Setup r} {policy : Policy c} {p q : ℝ}
    (h : IsValid c policy p q) :
    1 - p ≤ winProbability c policy c.initial ∧
      winProbability c policy c.initial ≤ 1 - q := by
  have heq := h.2.1.win_add_lose_eq_one
  have hf : loseProbability c policy c.initial ≤ p ∧
      q ≤ loseProbability c policy c.initial := h.2.2
  constructor <;> linarith

end MarkovRPG.Combat

namespace MarkovRPG.MarkovChain

variable {V Label : Type*} [Fintype V] (M : MarkovChain V Label)

/-- The eventual hitting probability solves the first-step equation outside the
target set. Finiteness permits exchanging the limit with the transition sum. -/
theorem hInf_step {s : V} (hs : s ∉ M.defeat) : M.hInf s = M.step M.hInf s := by
  have hn := tendsto_atTop_ciSup (M.h_mono s) (M.h_bddAbove s)
  have hshift := hn.comp (tendsto_add_atTop_nat 1)
  have hsum : Tendsto (fun n => M.step (M.h n) s) atTop (𝓝 (M.step M.hInf s)) := by
    unfold step
    exact tendsto_finsetSum _ (fun v _ => tendsto_const_nhds.mul
      (tendsto_atTop_ciSup (M.h_mono v) (M.h_bddAbove v)))
  apply tendsto_nhds_unique hshift
  simpa only [Function.comp_def, h_succ, if_neg hs, step] using hsum

theorem hInf_of_mem {s : V} (hs : s ∈ M.defeat) : M.hInf s = 1 := by
  apply le_antisymm (M.hInf_le_one s)
  simpa [h_zero, hs] using M.h_le_hInf 0 s

/-- A finite-graph termination certificate: from every vertex there is a path
of POSITIVE-probability edges to a target. No acyclicity or deterministic
duration bound is required. This is sufficient for all starting vertices. -/
theorem hInf_eq_one_of_reachable_target
    (reach : ∀ s, ∃ target ∈ M.defeat, Relation.ReflTransGen M.Edge s target)
    (start : V) : M.hInf start = 1 := by
  have : Nonempty V := ⟨M.initial⟩
  obtain ⟨v₀, _, hmin⟩ := Finset.exists_min_image Finset.univ M.hInf Finset.univ_nonempty
  have lower (v : V) : M.hInf v₀ ≤ M.hInf v := hmin v (Finset.mem_univ v)
  have propagate (s v : V) (hs : M.hInf s = M.hInf v₀) (edge : M.Edge s v) :
      M.hInf v = M.hInf v₀ := by
    by_cases htarget : s ∈ M.defeat
    · have hzero : M.hInf v₀ = 1 := hs.symm.trans (M.hInf_of_mem htarget)
      apply le_antisymm
      · rw [hzero]; exact M.hInf_le_one v
      · exact lower v
    · have nonneg (u : V) : 0 ≤ M.transition s u * (M.hInf u - M.hInf v₀) :=
        mul_nonneg (M.transition_nonneg s u) (sub_nonneg.mpr (lower u))
      have sumzero : ∑ u, M.transition s u * (M.hInf u - M.hInf v₀) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, M.transition_sum, one_mul]
        change M.step M.hInf s - M.hInf v₀ = 0
        rw [← M.hInf_step htarget, hs, sub_self]
      have termzero : M.transition s v * (M.hInf v - M.hInf v₀) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => nonneg u)).mp sumzero v
          (Finset.mem_univ v)
      exact sub_eq_zero.mp ((mul_eq_zero.mp termzero).resolve_left (ne_of_gt edge))
  obtain ⟨target, ht, path⟩ := reach v₀
  have heq : M.hInf target = M.hInf v₀ := by
    clear ht
    induction path with
    | refl => rfl
    | @tail b d path edge ih => exact propagate b d ih edge
  have hminone : M.hInf v₀ = 1 := heq.symm.trans (M.hInf_of_mem ht)
  apply le_antisymm (M.hInf_le_one start)
  simpa [hminone] using lower start

end MarkovRPG.MarkovChain

namespace MarkovRPG.Combat
variable {r : Rules}

/-- A graph-level certificate for all possible starting snapshots under a fixed
policy. `IsValid` itself only requires termination from the supplied initial state. -/
def CanReachOutput (c : Setup r) (policy : Policy c) : Prop :=
  ∀ s, ∃ target, target.output.isSome = true ∧
    Relation.ReflTransGen (c.chain policy none).Edge s target

theorem terminates_of_canReachOutput {c : Setup r} {policy : Policy c}
    (h : CanReachOutput c policy) (s : Vertex r) : IsTerminating c policy s := by
  exact (c.chain policy none).hInf_eq_one_of_reachable_target h s

end MarkovRPG.Combat
