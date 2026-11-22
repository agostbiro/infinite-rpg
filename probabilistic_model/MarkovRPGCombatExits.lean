import MarkovRPGCombatStrategies

/-!
# Exact, complete combat exits

The stopped finite-horizon law retains the final vertex, not merely Win/Lose.
Its terminal masses increase to an exact subprobability distribution. Its total
mass is the existing termination probability. A normalized exit law is available
only after almost-sure termination has been proved; nontermination is never
silently conditioned away. All definitions permit history-dependent strategies.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace MarkovRPG.Combat

variable {r : Rules} {c : Setup r}

/-- The finite law of total probability for an observation of a random value. -/
theorem pmf_map_toReal {α β : Type*} [Fintype α] (p : PMF α) (f : α → β) (b : β) :
    (p.map f b).toReal = ∑ a, if b = f a then (p a).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro a _
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top

namespace Game

/-- The state after at most `n` internal actions, stopped at the first output. -/
def stoppedLaw (g : Game c) : (n : Nat) → {s : Vertex r} → History c s → PMF (Vertex r)
  | 0, s, _ => PMF.pure s
  | n + 1, s, past =>
    if s.output.isSome then PMF.pure s
    else (g.choose past).bind (fun a =>
      (c.kernel s a.val).bindOnSupport (fun v hv =>
        g.stoppedLaw n (past.step a v hv)))

/-- Terminal mass by a finite horizon. Live states are not successful exits. -/
def exitBy (g : Game c) (n : Nat) {s : Vertex r} (past : History c s) (v : Vertex r) : ℝ :=
  if v.output.isSome then (g.stoppedLaw n past v).toReal else 0

theorem exitBy_nonneg (g : Game c) (n : Nat) {s : Vertex r}
    (past : History c s) (v : Vertex r) : 0 ≤ g.exitBy n past v := by
  unfold exitBy
  split <;> positivity

theorem exitBy_le_one (g : Game c) (n : Nat) {s : Vertex r}
    (past : History c s) (v : Vertex r) : g.exitBy n past v ≤ 1 := by
  unfold exitBy
  split
  · exact (ENNReal.toReal_le_toReal ((g.stoppedLaw n past).apply_ne_top v)
      ENNReal.one_ne_top).mpr ((g.stoppedLaw n past).coe_le_one v)
  · norm_num

theorem exitBy_zero (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    g.exitBy 0 past v = if s.output.isSome ∧ v = s then 1 else 0 := by
  by_cases hv : v = s
  · subst v
    cases hs : s.output <;> simp [exitBy, stoppedLaw, PMF.pure_apply, hs]
  · simp [exitBy, stoppedLaw, PMF.pure_apply, hv]

theorem step_zero (g : Game c) {s : Vertex r} (past : History c s) :
    g.step past (fun _ _ => 0) = 0 := by simp [step]

theorem exitBy_succ (g : Game c) (n : Nat) {s : Vertex r}
    (past : History c s) (v : Vertex r) :
    g.exitBy (n + 1) past v =
      if s.output.isSome then (if v = s then 1 else 0)
      else g.step past (fun _ next => g.exitBy n next v) := by
  cases hs : s.output with
  | some o =>
    by_cases hv : v = s
    · subst v
      simp [exitBy, stoppedLaw, hs, PMF.pure_apply]
    · simp [exitBy, stoppedLaw, hs, PMF.pure_apply, hv]
  | none =>
    cases hv : v.output with
    | none => simp [exitBy, hv, step_zero]
    | some o =>
      simp only [exitBy, hv, Option.isSome_some, if_true, stoppedLaw, hs,
        Option.isSome_none, Bool.false_eq_true, if_false]
      rw [pmf_bind_toReal]
      simp only [pmf_bindOnSupport_toReal, step]

theorem exitBy_terminal (g : Game c) (n : Nat) {s : Vertex r}
    (past : History c s) (o : Outcome) (hs : s.output = some o) (v : Vertex r) :
    g.exitBy n past v = if v = s then 1 else 0 := by
  cases n
  · simp [exitBy_zero, hs]
  · simp [exitBy_succ, hs]

theorem exitBy_mono (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    Monotone (fun n => g.exitBy n past v) := by
  have aux : ∀ n (s : Vertex r) (past : History c s),
      g.exitBy n past v ≤ g.exitBy (n + 1) past v := by
    intro n
    induction n with
    | zero =>
      intro s past
      cases hs : s.output with
      | some o => simp only [g.exitBy_terminal _ past o hs, le_refl]
      | none =>
        rw [exitBy_zero]
        simp only [hs, Option.isSome_none, Bool.false_eq_true, false_and, if_false]
        exact g.exitBy_nonneg 1 past v
    | succ n ih =>
      intro s past
      rw [exitBy_succ, exitBy_succ]
      split
      · exact le_rfl
      · exact g.step_mono past ih
  exact monotone_nat_of_le_succ (fun n => aux n s past)

theorem step_sum (g : Game c) {s : Vertex r} (past : History c s)
    {ι : Type*} (indices : Finset ι) (f : ι → (v : Vertex r) → History c v → ℝ) :
    g.step past (fun v h => ∑ i ∈ indices, f i v h) =
      ∑ i ∈ indices, g.step past (f i) := by
  induction indices using Finset.induction_on with
  | empty => simp [step_zero]
  | @insert i indices hi ih => simp only [Finset.sum_insert hi, step_add, ih]

/-- Recover each existing target probability by summing the complete exits. -/
theorem sum_exitBy (g : Game c) (goal : Option Outcome) (n : Nat) {s : Vertex r}
    (past : History c s) :
    (∑ v, if target goal v.output then g.exitBy n past v else 0) = g.h goal n past := by
  induction n generalizing s with
  | zero =>
    rw [h_zero]
    simp only [exitBy_zero]
    cases hs : s.output with
    | none => cases goal <;> simp [target]
    | some o =>
      have heq : (fun v : Vertex r =>
          if target goal v.output then (if (some o : Option Outcome).isSome ∧ v = s then (1 : ℝ) else 0)
          else 0) = fun v => if v = s then (if target goal (some o) then 1 else 0) else 0 := by
        funext v
        by_cases hv : v = s <;> simp [hv, hs]
      rw [heq]
      simp
  | succ n ih =>
    cases hs : s.output with
    | some o =>
      simp only [g.exitBy_terminal _ past o hs, g.h_terminal _ past o hs]
      have heq : (fun v : Vertex r =>
          if target goal v.output then (if v = s then (1 : ℝ) else 0) else 0) =
          fun v => if v = s then (if target goal (some o) then 1 else 0) else 0 := by
        funext v
        by_cases hv : v = s <;> simp [hv, hs]
      rw [heq]
      simp
    | none =>
      simp only [exitBy_succ, h_succ, hs, Option.isSome_none, Bool.false_eq_true, if_false]
      have heq : (fun v : Vertex r =>
          if target goal v.output then g.step past (fun _ next => g.exitBy n next v) else 0) =
          fun v => g.step past (fun _ next =>
            if target goal v.output then g.exitBy n next v else 0) := by
        funext v
        cases target goal v.output <;> simp [step_zero]
      rw [heq, ← step_sum]
      congr 1
      funext v next
      exact ih next

/-- Exact terminal subprobability, defined from the operational stopped laws. -/
def exitMass (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) : ℝ :=
  ⨆ n, g.exitBy n past v

theorem exitBy_bddAbove (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    BddAbove (Set.range (fun n => g.exitBy n past v)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact g.exitBy_le_one n past v⟩

theorem exitMass_nonneg (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    0 ≤ g.exitMass past v :=
  (g.exitBy_nonneg 0 past v).trans (le_ciSup (g.exitBy_bddAbove past v) 0)

theorem exitMass_le_one (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    g.exitMass past v ≤ 1 := ciSup_le (fun n => g.exitBy_le_one n past v)

theorem exitMass_tendsto (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    Tendsto (fun n => g.exitBy n past v) atTop (𝓝 (g.exitMass past v)) :=
  tendsto_atTop_ciSup (g.exitBy_mono past v) (g.exitBy_bddAbove past v)

/-- Win and Lose are marginals of the same complete exit law, even if the game
can fail to terminate. -/
theorem sum_exitMass (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) :
    (∑ v, if target goal v.output then g.exitMass past v else 0) = g.hInf goal past := by
  have hm : ∀ v : Vertex r, Tendsto
      (fun n => if target goal v.output then g.exitBy n past v else (0 : ℝ)) atTop
      (𝓝 (if target goal v.output then g.exitMass past v else 0)) := by
    intro v
    cases target goal v.output
    · exact tendsto_const_nhds
    · exact g.exitMass_tendsto past v
  have ht := tendsto_finsetSum Finset.univ (fun v _ => hm v)
  have hh := tendsto_atTop_ciSup (g.h_mono goal past) (g.h_bddAbove goal past)
  exact tendsto_nhds_unique ht (by simpa only [sum_exitBy, hInf] using hh)

theorem exitMass_live (g : Game c) {s : Vertex r} (past : History c s)
    (v : Vertex r) (hv : v.output = none) : g.exitMass past v = 0 := by
  simp [exitMass, exitBy, hv]

theorem total_exitMass (g : Game c) {s : Vertex r} (past : History c s) :
    (∑ v, g.exitMass past v) = g.hInf none past := by
  rw [← g.sum_exitMass none past]
  apply Finset.sum_congr rfl
  intro v _
  cases hv : v.output
  · simp [target, g.exitMass_live past v hv]
  · simp [target]

/-- Only vertices connected to the actual entry can have positive probability. -/
theorem stoppedLaw_reachable (g : Game c) (n : Nat) {s : Vertex r}
    (past : History c s) (v : Vertex r) (hv : v ∈ (g.stoppedLaw n past).support) :
    Nonempty (History c v) := by
  induction n generalizing s with
  | zero =>
    have he : v = s := (PMF.mem_support_pure_iff _ _).mp hv
    subst v
    exact ⟨past⟩
  | succ n ih =>
    unfold stoppedLaw at hv
    split at hv
    · have he : v = s := (PMF.mem_support_pure_iff _ _).mp hv
      subst v
      exact ⟨past⟩
    · rw [PMF.mem_support_bind_iff] at hv
      obtain ⟨a, _, hv⟩ := hv
      rw [PMF.mem_support_bindOnSupport_iff] at hv
      obtain ⟨w, hw, hv⟩ := hv
      exact ih (past.step a w hw) hv

theorem exitMass_unreachable (g : Game c) {s : Vertex r} (past : History c s)
    (v : Vertex r) (hv : ¬ Nonempty (History c v)) : g.exitMass past v = 0 := by
  have hz : ∀ n, g.stoppedLaw n past v = 0 := by
    intro n
    by_contra h
    exact hv (g.stoppedLaw_reachable n past v h)
  simp [exitMass, exitBy, hz]

/-- This is a probability law only under a termination proof. Its probabilities
are unchanged terminal masses, not renormalized conditional probabilities. -/
def terminalLaw (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) : PMF (Vertex r) :=
  PMF.ofFintype (fun v => ENNReal.ofReal (g.exitMass past v)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => g.exitMass_nonneg past v),
      g.total_exitMass past, terminates, ENNReal.ofReal_one])

@[simp] theorem terminalLaw_apply (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) (v : Vertex r) :
    (g.terminalLaw past terminates v).toReal = g.exitMass past v :=
  ENNReal.toReal_ofReal (g.exitMass_nonneg past v)

theorem terminalLaw_support (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) (v : Vertex r)
    (hv : v ∈ (g.terminalLaw past terminates).support) :
    Nonempty (History c v) ∧ v.output.isSome = true := by
  have hn : g.exitMass past v ≠ 0 := by
    intro hz
    apply hv
    change ENNReal.ofReal (g.exitMass past v) = 0
    simp [hz]
  constructor
  · by_contra hr
    exact hn (g.exitMass_unreachable past v hr)
  · cases ho : v.output with
    | none => exact False.elim (hn (g.exitMass_live past v ho))
    | some o => rfl

end Game

/-- The complete dynamic character view at an event boundary. Empty stocks and
zero timers are retained in their stable slots. Item descriptors and effect
sources are not discarded, renumbered, or folded into base statistics. This
format avoids truncating the output to the smaller list of *initial* effects.
`c` fixes the binding of source keys to the actual characters and items. -/
structure CharacterResult (r : Rules) where
  id : CharacterId
  statistics : Statistics
  equipment : Equipment
  resources : List (ResourceId × Nat)
  hp : Fin (r.hpMax + 1)
  items : Fin r.itemSlots → Option ItemMechanics
  stock : Fin r.itemSlots → Fin (r.stockMax + 1)
  modifiers : EffectKey r → Option Modifier
  remaining : EffectKey r → Fin (r.durationMax + 1)

def Setup.characterResult (c : Setup r) (v : Vertex r) (p : Player) : CharacterResult r where
  id := (c.characters p).character.id
  statistics := (c.characters p).character.statistics
  equipment := (c.characters p).character.equipment
  resources := (c.characters p).character.resources
  hp := v.hp p
  items := c.item? p
  stock := v.stock p
  modifiers := c.modifier?
  remaining := v.remaining p

theorem Setup.characterResult_preserves (c : Setup r) (v : Vertex r) (p : Player) :
    (c.characterResult v p).id = (c.characters p).character.id ∧
    (c.characterResult v p).statistics = (c.characters p).character.statistics ∧
    (c.characterResult v p).equipment = (c.characters p).character.equipment ∧
    (c.characterResult v p).resources = (c.characters p).character.resources ∧
    (c.characterResult v p).items = c.item? p ∧
    (c.characterResult v p).modifiers = c.modifier? ∧
    (c.characterResult v p).hp = v.hp p ∧
    (c.characterResult v p).stock = v.stock p ∧
    (c.characterResult v p).remaining = v.remaining p := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CharacterResult.bounds (x : CharacterResult r) :
    x.hp.val ≤ r.hpMax ∧
    (∀ i, (x.stock i).val ≤ r.stockMax) ∧
    (∀ key, (x.remaining key).val ≤ r.durationMax) :=
  ⟨Nat.le_of_lt_succ x.hp.isLt, fun i => Nat.le_of_lt_succ (x.stock i).isLt,
    fun key => Nat.le_of_lt_succ (x.remaining key).isLt⟩

/-- A full exit is a reachable terminal vertex. The outcome and both characters
are derived from it, so they cannot disagree with the actual combat result. -/
def FullExit (c : Setup r) :=
  {v : Vertex r // Nonempty (History c v) ∧ v.output.isSome = true}

instance : Fintype (FullExit c) := inferInstanceAs (Fintype {v : Vertex r //
  Nonempty (History c v) ∧ v.output.isSome = true})

def FullExit.outcome (o : FullExit c) : Outcome := o.val.output.get o.property.2

def FullExit.character (o : FullExit c) (p : Player) : CharacterResult r :=
  c.characterResult o.val p

theorem FullExit.output_eq (o : FullExit c) : o.val.output = some o.outcome := by
  exact (Option.some_get o.property.2).symm

theorem FullExit.win_iff (o : FullExit c) :
    o.outcome = .Win ↔ 0 < (o.character .A).hp.val ∧ (o.character .B).hp.val = 0 := by
  have h := o.val.output_win_iff
  rw [o.output_eq, Option.some.injEq] at h
  exact h

theorem FullExit.lose_iff (o : FullExit c) :
    o.outcome = .Lose ↔ (o.character .A).hp.val = 0 := by
  have h := o.val.output_lose_iff
  rw [o.output_eq, Option.some.injEq] at h
  exact h

namespace Game

/-- Attach the proved reachability and terminal invariants to each sampled exit. -/
def resolve (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) : PMF (FullExit c) :=
  (g.terminalLaw past terminates).bindOnSupport (fun v hv =>
    PMF.pure ⟨v, g.terminalLaw_support past terminates v hv⟩)

/-- Removing proof fields gives exactly the operational exit law. -/
theorem resolve_map_vertex (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) :
    (g.resolve past terminates).map Subtype.val = g.terminalLaw past terminates := by
  unfold resolve PMF.map
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.pure_bindOnSupport, Function.comp_apply, PMF.bindOnSupport_pure]

@[simp] theorem resolve_apply (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) (o : FullExit c) :
    (g.resolve past terminates o).toReal = g.exitMass past o.val := by
  have h := congrArg (fun p : PMF (Vertex r) => p o.val)
    (g.resolve_map_vertex past terminates)
  simp only [PMF.map_apply, Subtype.val_inj, tsum_ite_eq'] at h
  exact (congrArg ENNReal.toReal h).trans (g.terminalLaw_apply past terminates o.val)

theorem resolve_map_output (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) :
    ((g.resolve past terminates).map FullExit.outcome).map some =
      (g.terminalLaw past terminates).map Vertex.output := by
  rw [← g.resolve_map_vertex past terminates, PMF.map_comp, PMF.map_comp]
  congr 1
  funext o
  exact o.output_eq.symm

/-- The full exit law has exactly the previously defined Win/Lose probabilities. -/
theorem resolve_outcome (g : Game c) {s : Vertex r} (past : History c s)
    (terminates : g.hInf none past = 1) (outcome : Outcome) :
    ((g.resolve past terminates).map FullExit.outcome outcome).toReal =
      g.hInf (some outcome) past := by
  have he := congrArg (fun p : PMF (Option Outcome) => (p (some outcome)).toReal)
    (g.resolve_map_output past terminates)
  have hlift : ∀ p : PMF Outcome, p.map some (some outcome) = p outcome := by
    intro p
    simp only [PMF.map_apply, Option.some.injEq, tsum_ite_eq']
  rw [hlift] at he
  conv_rhs at he => rw [pmf_map_toReal]
  simp only [terminalLaw_apply] at he
  rw [he, ← g.sum_exitMass (some outcome) past]
  apply Finset.sum_congr rfl
  intro v _
  cases hv : v.output with
  | none => simp [target]
  | some o => cases o <;> cases outcome <;> simp [target]

/-- With a stationary policy the event edge is computed at the actual entry
vertex, including its exact HP, stocks and timers. -/
theorem Represents.resolve_outcome {g : Game c} {policy : Policy c}
    (rep : g.Represents policy) (terminates : g.hInf none History.root = 1)
    (outcome : Outcome) :
    ((g.resolve History.root terminates).map FullExit.outcome outcome).toReal =
      (c.chain policy (some outcome)).hInf c.initial := by
  rw [g.resolve_outcome, rep.hInf_eq]

theorem uniform_resolve_outcome (c : Setup r)
    (terminates : (uniform c).hInf none History.root = 1) (outcome : Outcome) :
    (((uniform c).resolve History.root terminates).map FullExit.outcome outcome).toReal =
      (c.chain (uniformPolicy c) (some outcome)).hInf c.initial :=
  Represents.resolve_outcome (uniform_represents c) terminates outcome

end Game
end MarkovRPG.Combat
