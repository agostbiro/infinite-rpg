import MarkovRPGCombatTheorems

/-!
# History-dependent combat strategies

A history is an inductive, action-labelled walk from the supplied initial
vertex. Every extension has an enabled action and a positive-probability
outcome of the existing combat kernel. Vertices may repeat: cycles are legal.

A behavioral strategy assigns an exact distribution to available actions at
each history where its character acts. The kernel then determines the resulting
vertex. Memorylessness may retain the absolute time; stationary memorylessness
factors through the current vertex alone. Only the latter yields the existing
homogeneous finite Markov chain without extending its state.

The game below accepts one strategy per character. Finite-horizon risks are
probabilities of genuine PMFs; eventual risks are their monotone suprema.
No sampling, confidence interval, or automatic termination assumption is used.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace MarkovRPG.Combat

variable {r : Rules}

/-- A rooted walk, indexed by its endpoint. Chance outcomes are recorded as
vertices; the action label distinguishes different decisions with the same end.
The graph is independent of a strategy, which can give some legal paths mass zero.
Absorbing self-loops may extend terminal paths; they cannot change the result. -/
inductive History (c : Setup r) : Vertex r → Type where
  | root : History c c.initial
  | step {s : Vertex r} (past : History c s)
      (action : {a : Action r // c.enabled s a = true}) (next : Vertex r)
      (possible : next ∈ (c.kernel s action.val).support) : History c next

def History.length {c : Setup r} {s : Vertex r} : History c s → Nat
  | .root => 0
  | .step past _ _ _ => past.length + 1

@[simp] theorem History.length_root (c : Setup r) : (History.root (c := c)).length = 0 := rfl

@[simp] theorem History.length_step {c : Setup r} {s : Vertex r} (h : History c s)
    (a : {a : Action r // c.enabled s a = true}) (v : Vertex r)
    (hv : v ∈ (c.kernel s a.val).support) : (h.step a v hv).length = h.length + 1 := rfl

/-- The player's identity is `c.characters player`; the strategy observes the
entire public history of states and actions, not unrecorded random rolls. -/
structure Strategy (c : Setup r) (player : Player) where
  choose : {s : Vertex r} → History c s → s.turn = player →
    PMF {a : Action r // c.enabled s a = true}

namespace Strategy
variable {c : Setup r} {player : Player}

/-- The current time and vertex suffice to make a decision. -/
def IsMemoryless (σ : Strategy c player) : Prop :=
  ∃ rule : (t : Nat) → (s : Vertex r) → s.turn = player →
      PMF {a : Action r // c.enabled s a = true},
    ∀ {s} (h : History c s) (turn : s.turn = player),
      σ.choose h turn = rule h.length s turn

/-- The current vertex alone suffices, at every time and every legal history. -/
def IsStationaryMemoryless (σ : Strategy c player) : Prop :=
  ∃ rule : (s : Vertex r) → s.turn = player →
      PMF {a : Action r // c.enabled s a = true},
    ∀ {s} (h : History c s) (turn : s.turn = player), σ.choose h turn = rule s turn

theorem IsStationaryMemoryless.isMemoryless {σ : Strategy c player}
    (hσ : σ.IsStationaryMemoryless) : σ.IsMemoryless := by
  obtain ⟨rule, h⟩ := hσ
  exact ⟨fun _ => rule, h⟩

theorem IsMemoryless.choose_eq {σ : Strategy c player} (hσ : σ.IsMemoryless)
    {s : Vertex r} (past other : History c s) (sameTime : past.length = other.length)
    (turn : s.turn = player) : σ.choose past turn = σ.choose other turn := by
  obtain ⟨rule, hrule⟩ := hσ
  rw [hrule past turn, hrule other turn, sameTime]

theorem IsStationaryMemoryless.choose_eq {σ : Strategy c player}
    (hσ : σ.IsStationaryMemoryless) {s : Vertex r} (past other : History c s)
    (turn : s.turn = player) : σ.choose past turn = σ.choose other turn := by
  obtain ⟨rule, hrule⟩ := hσ
  rw [hrule past turn, hrule other turn]

/-- Deterministic strategies are included as Dirac distributions. -/
def deterministic (rule : {s : Vertex r} → History c s → s.turn = player →
    {a : Action r // c.enabled s a = true}) : Strategy c player where
  choose h turn := PMF.pure (rule h turn)

/-- Restrict an existing joint policy to one player's turns. -/
def ofPolicy (policy : Policy c) (player : Player) : Strategy c player where
  choose {s} _ _ := policy.choose s

theorem ofPolicy_stationary (policy : Policy c) (player : Player) :
    (ofPolicy policy player).IsStationaryMemoryless :=
  ⟨fun s _ => policy.choose s, fun _ _ => rfl⟩

/-- Uniform over concrete enabled actions, including each usable item slot.
This reuses the existing uniform law rather than implementing it twice. -/
def uniform (c : Setup r) (player : Player) : Strategy c player :=
  ofPolicy (uniformPolicy c) player

theorem uniform_stationary (c : Setup r) (player : Player) :
    (uniform c player).IsStationaryMemoryless := ofPolicy_stationary _ _

theorem uniform_apply {s : Vertex r} (h : History c s) (turn : s.turn = player)
    (a : {a : Action r // c.enabled s a = true}) :
    (uniform c player).choose h turn a =
      (Fintype.card {a : Action r // c.enabled s a = true} : ℝ≥0∞)⁻¹ := by
  let : Nonempty {a : Action r // c.enabled s a = true} := ⟨⟨.attack, rfl⟩⟩
  exact PMF.uniformOfFintype_apply a

end Strategy

/-- The combat mechanics remain in `c`; only the characters' decisions are added. -/
structure Game (c : Setup r) where
  strategies : (player : Player) → Strategy c player

namespace Game
variable {c : Setup r}

def choose (g : Game c) {s : Vertex r} (h : History c s) :
    PMF {a : Action r // c.enabled s a = true} :=
  (g.strategies s.turn).choose h rfl

/-- The next-state distribution induced by a history-dependent decision. -/
def nextState (g : Game c) {s : Vertex r} (h : History c s) : PMF (Vertex r) :=
  (g.choose h).bind (fun a => c.kernel s a.val)

def ofPolicy (policy : Policy c) : Game c := ⟨Strategy.ofPolicy policy⟩

def uniform (c : Setup r) : Game c := ⟨Strategy.uniform c⟩

/-- A finite-state policy represents the game on every legal rooted history.
No condition on arbitrary unreachable vertices is smuggled into a strategy. -/
def Represents (g : Game c) (policy : Policy c) : Prop :=
  ∀ {s} (h : History c s), g.choose h = policy.choose s

theorem ofPolicy_represents (policy : Policy c) : (ofPolicy policy).Represents policy :=
  fun _ => rfl

theorem exists_policy_of_stationary (g : Game c)
    (hσ : ∀ player, (g.strategies player).IsStationaryMemoryless) :
    ∃ policy : Policy c, g.Represents policy := by
  let policy : Policy c :=
    ⟨fun s => Classical.choose (hσ s.turn) s rfl⟩
  refine ⟨policy, ?_⟩
  intro s h
  exact Classical.choose_spec (hσ s.turn) h rfl

theorem Represents.nextState_eq {g : Game c} {policy : Policy c}
    (rep : g.Represents policy) {s : Vertex r} (h : History c s) :
    g.nextState h = c.row policy s := by
  simp only [nextState, Setup.row, rep h]

theorem uniform_represents (c : Setup r) : (uniform c).Represents (uniformPolicy c) :=
  fun _ => rfl

/-- The target can be one output or either terminal output. -/
def target (goal output : Option Outcome) : Bool := match goal with
  | none => output.isSome
  | some o => output == some o

/-- Exact finite-horizon law of the event of reaching the target. The recursive
continuation retains the full path, including the chosen action. Terminal
histories stop immediately. Impossible chance branches are never evaluated. -/
def hitLaw (g : Game c) (goal : Option Outcome) :
    (n : Nat) → {s : Vertex r} → History c s → PMF Bool
  | 0, s, _ => PMF.pure (target goal s.output)
  | n + 1, s, h =>
    if s.output.isSome then PMF.pure (target goal s.output)
    else (g.choose h).bind (fun a =>
      (c.kernel s a.val).bindOnSupport (fun v hv => g.hitLaw goal n (h.step a v hv)))

def h (g : Game c) (goal : Option Outcome) (n : Nat) {s : Vertex r}
    (past : History c s) : ℝ := (g.hitLaw goal n past true).toReal

theorem h_nonneg (g : Game c) (goal : Option Outcome) (n : Nat) {s : Vertex r}
    (past : History c s) : 0 ≤ g.h goal n past := ENNReal.toReal_nonneg

theorem h_le_one (g : Game c) (goal : Option Outcome) (n : Nat) {s : Vertex r}
    (past : History c s) : g.h goal n past ≤ 1 := by
  exact (ENNReal.toReal_le_toReal (g.hitLaw goal n past |>.apply_ne_top true)
    ENNReal.one_ne_top).mpr (g.hitLaw goal n past |>.coe_le_one true)

theorem h_zero (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) : g.h goal 0 past = if target goal s.output then 1 else 0 := by
  cases ht : target goal s.output <;> simp [h, hitLaw, ht, PMF.pure_apply]

end Game

/-- Finite exact expectation under a PMF bind. -/
theorem pmf_bind_toReal {α β : Type*} [Fintype α] (p : PMF α) (f : α → PMF β) (b : β) :
    (p.bind f b).toReal = ∑ a, (p a).toReal * (f a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top b)

theorem pmf_bindOnSupport_toReal {α β : Type*} [Fintype α] (p : PMF α)
    (f : ∀ a ∈ p.support, PMF β) (b : β) :
    (p.bindOnSupport f b).toReal =
      ∑ a, if ha : p a = 0 then 0 else (p a).toReal * (f a ha b).toReal := by
  rw [PMF.bindOnSupport_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : p a = 0 <;> simp [ha, ENNReal.toReal_mul]
  · intro a _
    split_ifs with ha
    · simp
    · exact ENNReal.mul_ne_top (p.apply_ne_top a) ((f a ha).apply_ne_top b)

namespace Game
variable {c : Setup r}

/-- The strategy's action probabilities and the kernel's outcome probabilities
combine by the law of total probability. -/
theorem nextState_apply (g : Game c) {s : Vertex r} (past : History c s) (v : Vertex r) :
    (g.nextState past v).toReal =
      ∑ a, (g.choose past a).toReal * (c.kernel s a.val v).toReal :=
  pmf_bind_toReal _ _ _

theorem nextState_absorbing (g : Game c) {s : Vertex r} (past : History c s)
    (o : Outcome) (hs : s.output = some o) : g.nextState past = PMF.pure s := by
  simp [nextState, c.kernel_absorbing s o hs, PMF.bind_const]

/-- One step of exact expectation, keeping the path in the continuation. -/
def step (g : Game c) {s : Vertex r} (past : History c s)
    (f : (v : Vertex r) → History c v → ℝ) : ℝ :=
  ∑ a, (g.choose past a).toReal * ∑ v,
    if hv : c.kernel s a.val v = 0 then 0
    else (c.kernel s a.val v).toReal * f v (past.step a v hv)

theorem h_succ (g : Game c) (goal : Option Outcome) (n : Nat) {s : Vertex r}
    (past : History c s) :
    g.h goal (n + 1) past =
      if s.output.isSome then (if target goal s.output then 1 else 0)
      else g.step past (fun _ next => g.h goal n next) := by
  cases hs : s.output with
  | none =>
    simp only [h, hitLaw, hs, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [pmf_bind_toReal]
    simp only [pmf_bindOnSupport_toReal, step]
  | some o =>
    cases ht : target goal (some o) <;> simp [h, hitLaw, hs, ht, PMF.pure_apply]

theorem step_mono (g : Game c) {s : Vertex r} (past : History c s)
    {f k : (v : Vertex r) → History c v → ℝ}
    (hf : ∀ v h, f v h ≤ k v h) : g.step past f ≤ g.step past k := by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply Finset.sum_le_sum
  intro v _
  split_ifs with hv
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (hf v _) ENNReal.toReal_nonneg

theorem step_add (g : Game c) {s : Vertex r} (past : History c s)
    (f k : (v : Vertex r) → History c v → ℝ) :
    g.step past (fun v h => f v h + k v h) = g.step past f + g.step past k := by
  unfold step
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

/-- Forgetting the path in the continuation gives the usual next-state expectation. -/
theorem step_state_function (g : Game c) {s : Vertex r} (past : History c s)
    (f : Vertex r → ℝ) :
    g.step past (fun v _ => f v) = ∑ v, (g.nextState past v).toReal * f v := by
  unfold step nextState
  simp_rw [pmf_bind_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : c.kernel s a.val v = 0 <;> simp [hv, mul_assoc]

theorem h_terminal (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) (o : Outcome) (hs : s.output = some o) (n : Nat) :
    g.h goal n past = if target goal (some o) then 1 else 0 := by
  cases n <;> cases ht : target goal (some o) <;>
    simp [h, hitLaw, hs, ht, PMF.pure_apply]

theorem h_mono (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) : Monotone (fun n => g.h goal n past) := by
  have aux : ∀ n (s : Vertex r) (past : History c s),
      g.h goal n past ≤ g.h goal (n + 1) past := by
    intro n
    induction n with
    | zero =>
      intro s past
      cases hs : s.output with
      | some o => simp only [g.h_terminal goal past o hs, le_refl]
      | none =>
        have hz : g.h goal 0 past = 0 := by
          rw [h_zero, hs]
          cases goal <;> simp [target]
        rw [hz]
        exact g.h_nonneg goal 1 past
    | succ n ih =>
      intro s past
      rw [h_succ, h_succ]
      split
      · exact le_rfl
      · exact g.step_mono past ih
  exact monotone_nat_of_le_succ (fun n => aux n s past)

/-- Exact eventual probability, including possible mass at nontermination. -/
def hInf (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) : ℝ := ⨆ n, g.h goal n past

theorem h_bddAbove (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) : BddAbove (Set.range (fun n => g.h goal n past)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact g.h_le_one goal n past⟩

theorem h_le_hInf (g : Game c) (goal : Option Outcome) (n : Nat) {s : Vertex r}
    (past : History c s) : g.h goal n past ≤ g.hInf goal past :=
  le_ciSup (g.h_bddAbove goal past) n

theorem hInf_nonneg (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) : 0 ≤ g.hInf goal past :=
  (g.h_nonneg goal 0 past).trans (g.h_le_hInf goal 0 past)

theorem hInf_le_one (g : Game c) (goal : Option Outcome) {s : Vertex r}
    (past : History c s) : g.hInf goal past ≤ 1 :=
  ciSup_le (fun n => g.h_le_one goal n past)

/-- The target predicate agrees with the existing finite graph's target set. -/
theorem target_eq_true_iff (policy : Policy c) (goal : Option Outcome) (s : Vertex r) :
    target goal s.output = true ↔ s ∈ (c.chain policy goal).defeat := by
  cases goal <;> simp [target, Setup.chain]

/-- Reduction theorem: a stationary representation preserves the entire
finite-horizon risk curve, from every legal history, not only from the root. -/
theorem Represents.h_eq {g : Game c} {policy : Policy c} (rep : g.Represents policy)
    (goal : Option Outcome) (n : Nat) {s : Vertex r} (past : History c s) :
    g.h goal n past = (c.chain policy goal).h n s := by
  induction n generalizing s with
  | zero =>
    rw [h_zero, MarkovChain.h_zero]
    simp only [target_eq_true_iff policy]
  | succ n ih =>
    cases hs : s.output with
    | some o =>
      rw [g.h_terminal goal past o hs, c.h_terminal policy s o hs]
      cases goal <;> cases o <;> simp [target, Setup.chain, hs]
    | none =>
      have hn : s ∉ (c.chain policy goal).defeat := by
        cases goal <;> simp [Setup.chain, hs]
      simp only [h_succ, hs, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [MarkovChain.h_succ, if_neg hn]
      have hc : (fun v (next : History c v) => g.h goal n next) =
          (fun v (_ : History c v) => (c.chain policy goal).h n v) := by
        funext v next
        exact ih next
      rw [hc, step_state_function, rep.nextState_eq]
      rfl

theorem Represents.hInf_eq {g : Game c} {policy : Policy c} (rep : g.Represents policy)
    (goal : Option Outcome) {s : Vertex r} (past : History c s) :
    g.hInf goal past = (c.chain policy goal).hInf s := by
  simp only [hInf, MarkovChain.hInf, rep.h_eq]

/-- Existence of a finite Markov representation follows from the individual
strategies' factorization. General history-dependent strategies are not assumed
to have such a representation. -/
theorem stationary_reduction (g : Game c)
    (hσ : ∀ player, (g.strategies player).IsStationaryMemoryless) :
    ∃ policy : Policy c, g.Represents policy ∧
      ∀ goal n (s : Vertex r) (past : History c s),
        g.h goal n past = (c.chain policy goal).h n s := by
  obtain ⟨policy, rep⟩ := g.exists_policy_of_stationary hσ
  exact ⟨policy, rep, fun goal n _ past => rep.h_eq goal n past⟩

/-- Finite termination partitions into the two disjoint outputs for arbitrary
history-dependent strategies. -/
theorem win_add_lose_by (g : Game c) (n : Nat) {s : Vertex r} (past : History c s) :
    g.h (some .Win) n past + g.h (some .Lose) n past = g.h none n past := by
  induction n generalizing s with
  | zero =>
    simp only [h_zero]
    cases hs : s.output with
    | none => simp [target]
    | some o => cases o <;> simp [target]
  | succ n ih =>
    cases hs : s.output with
    | some o =>
      simp only [g.h_terminal _ past o hs]
      cases o <;> simp [target]
    | none =>
      simp only [h_succ, hs, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [← step_add]
      congr 1
      funext v next
      exact ih next

theorem win_add_lose (g : Game c) {s : Vertex r} (past : History c s) :
    g.hInf (some .Win) past + g.hInf (some .Lose) past = g.hInf none past := by
  change (⨆ n, g.h (some .Win) n past) + (⨆ n, g.h (some .Lose) n past) =
    ⨆ n, g.h none n past
  have hw := tendsto_atTop_ciSup (g.h_mono (some .Win) past)
    (g.h_bddAbove (some .Win) past)
  have hl := tendsto_atTop_ciSup (g.h_mono (some .Lose) past)
    (g.h_bddAbove (some .Lose) past)
  have ht := tendsto_atTop_ciSup (g.h_mono none past) (g.h_bddAbove none past)
  exact tendsto_nhds_unique (hw.add hl) (by simpa only [win_add_lose_by] using ht)

/-- The same acceptance contract, now for strategies with arbitrary history
dependence: live inputs, almost-sure termination, and exact loss risk in [q,p]. -/
def IsValid (g : Game c) (p q : ℝ) : Prop :=
  c.initial.output = none ∧ g.hInf none .root = 1 ∧
    g.hInf (some .Lose) .root ≤ p ∧ q ≤ g.hInf (some .Lose) .root

theorem isValid_iff_input_contract (g : Game c) (p q : ℝ) :
    g.IsValid p q ↔
      (∀ player, 0 < (c.characters player).character.hp) ∧
      g.hInf none .root = 1 ∧
      q ≤ g.hInf (some .Lose) .root ∧ g.hInf (some .Lose) .root ≤ p := by
  rw [IsValid, c.initial_alive_iff]
  tauto

theorem IsValid.win_band {g : Game c} {p q : ℝ} (valid : g.IsValid p q) :
    1 - p ≤ g.hInf (some .Win) .root ∧ g.hInf (some .Win) .root ≤ 1 - q := by
  have heq := g.win_add_lose History.root
  have ht := valid.2.1
  have upper := valid.2.2.1
  have lower := valid.2.2.2
  constructor <;> linarith

theorem Represents.isValid_iff {g : Game c} {policy : Policy c} (rep : g.Represents policy)
    (p q : ℝ) : g.IsValid p q ↔ Combat.IsValid c policy p q := by
  simp only [IsValid, Combat.IsValid, IsTerminating, IsFair, terminationProbability,
    MarkovChain.IsMarkovpqFair, rep.hInf_eq]

/-- Exact recovery of the original uniform game's finite-horizon probabilities. -/
theorem uniform_h_eq (c : Setup r) (goal : Option Outcome) (n : Nat)
    {s : Vertex r} (past : History c s) :
    (uniform c).h goal n past = (c.chain (uniformPolicy c) goal).h n s :=
  Represents.h_eq (uniform_represents c) goal n past

theorem uniform_hInf_eq (c : Setup r) (goal : Option Outcome)
    {s : Vertex r} (past : History c s) :
    (uniform c).hInf goal past = (c.chain (uniformPolicy c) goal).hInf s :=
  Represents.hInf_eq (uniform_represents c) goal past

theorem uniform_isValid_iff (c : Setup r) (p q : ℝ) :
    (uniform c).IsValid p q ↔ Combat.IsValid c (uniformPolicy c) p q :=
  Represents.isValid_iff (uniform_represents c) p q

end Game
end MarkovRPG.Combat
