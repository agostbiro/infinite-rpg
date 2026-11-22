import MarkovRPGNamedDistributions

/-!
# Exact certificates for the local graph workshop

Sparse rational rows are the executable interchange format. Their real-valued
interpretation is the existing MarkovChain, not a separate notion of fairness.
The external solver proposes rational solutions; Lean checks their equations,
positive paths to outputs, and the complete finite-horizon duration certificate.
-/

open scoped BigOperators NNReal
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace MarkovRPG.Workshop

def weight {n : ℕ} (row : List (Fin n × ℚ)) (v : Fin n) : ℚ :=
  (row.map fun e => if e.1 = v then e.2 else 0).sum

def dot {n : ℕ} (row : List (Fin n × ℚ)) (f : Fin n → ℚ) : ℚ :=
  (row.map fun e => e.2 * f e.1).sum

structure Graph (n : ℕ) where
  initial : Fin n
  rows : Fin n → List (Fin n × ℚ)
  terminal : Fin n → Bool
  lose : Fin n → Bool
  nonneg : ∀ s e, e ∈ rows s → 0 ≤ e.2
  normalized : ∀ s, ((rows s).map Prod.snd).sum = 1
  loss_terminal : ∀ s, lose s = true → terminal s = true
  absorbing : ∀ s, terminal s = true → rows s = [(s, 1)]

/-! The first executable profile is deliberately bounded: unarmed characters
with ST10, HT10, no items or active modifiers, and HP in 0..3 under common HPmax6.
Attack and Defend are uniformly selected. MainRules supplies success, dodge,
weapon damage, critical success and crushing injury; no Monte Carlo is involved.
The full item/effect combat model remains available in MarkovRPGCombat. -/

def prototypeBeing (level : ℕ) : MainRules.Being :=
  ⟨"fighter", 10, level, 10, 10, [], .punch, .none, 0⟩

def prototypeRules : Combat.Rules where
  hpMax := 6
  itemSlots := 0
  effectsPerSource := 0
  stockMax := 0
  durationMax := 0

def prototypeCharacter (id hp level : ℕ) : CharacterStateCombat where
  id := ⟨id⟩
  statistics := ⟨10, level, 10, 10, [], 0⟩
  inventory := []
  equipment := ⟨none, none⟩
  hp := hp
  effects := []
  resources := []

theorem prototypeCharacter_admissible : ∀ hp : Fin 4, ∀ level : Fin 21,
    (prototypeCharacter 1 hp.val level.val).WellFormed prototypeRules := by decide +kernel

def faces3 : List (ℕ × ℚ) :=
  [(3,1/216), (4,3/216), (5,6/216), (6,10/216), (7,15/216), (8,21/216),
   (9,25/216), (10,27/216), (11,27/216), (12,25/216), (13,21/216),
   (14,15/216), (15,10/216), (16,6/216), (17,3/216), (18,1/216)]

/-- The table is checked against all 216 equally likely ordered triples. -/
theorem faces3_count : ∀ r : Fin 19,
    ((faces3.filter (fun e => e.1 == r.val)).map Prod.snd).sum =
      ((List.range 6).flatMap fun a => (List.range 6).flatMap fun b =>
        (List.range 6).map fun c => if a + b + c + 3 = r.val then (1/216 : ℚ) else 0).sum := by
  decide +kernel

def rollProbability (predicate : ℕ → Bool) : ℚ :=
  ((faces3.filter (fun e => predicate e.1)).map Prod.snd).sum

def duelHP (s : Fin 64) : ℕ × ℕ := (s.val / 16, s.val / 4 % 4)
def duelTurn (s : Fin 64) : ℕ := s.val / 2 % 2
def duelGuard (s : Fin 64) : Bool := s.val % 2 == 1
def duelTerminal (s : Fin 64) : Bool := (duelHP s).1 == 0 || (duelHP s).2 == 0
def duelLose (s : Fin 64) : Bool := (duelHP s).1 == 0
def duelOutput (s : Fin 64) : ℕ := if duelLose s then 0 else (duelHP s).1

def duelIndex (hpA hpB turn : ℕ) (guard : Bool) : Fin 64 :=
  ⟨(((hpA * 4 + hpB) * 2 + turn) * 2 + if guard then 1 else 0) % 64, Nat.mod_lt _ (by decide)⟩

theorem duelIndex_decode : ∀ s : Fin 64,
    duelIndex (duelHP s).1 (duelHP s).2 (duelTurn s) (duelGuard s) = s := by decide

def duelRows (enemyLevel : ℕ) (s : Fin 64) : List (Fin 64 × ℚ) :=
  if duelTerminal s then [(s, 1)] else
  let a := (duelHP s).1
  let b := (duelHP s).2
  let turn := duelTurn s
  let actor := prototypeBeing (if turn = 0 then 12 else enemyLevel)
  let defender := prototypeBeing (if turn = 0 then enemyLevel else 12)
  let defenderHP := if turn = 0 then b else a
  let dodge := (if 3 * defenderHP < 6 then (defender.dodge + 1) / 2 else defender.dodge) +
    if duelGuard s then 2 else 0
  let dodgeP := rollProbability (fun roll => (MainRules.successRoll dodge roll).succeeded)
  let ordinary := rollProbability (fun roll => MainRules.successRoll actor.attackLevel roll == .success)
  let otherCritical := rollProbability (fun roll =>
    roll != 3 && MainRules.successRoll actor.attackLevel roll == .criticalSuccess)
  let maximized : ℚ := 1/216
  let hit := otherCritical + ordinary * (1 - dodgeP)
  let next := fun amount => if turn = 0 then duelIndex a (b - amount) 1 false
    else duelIndex (a - amount) b 0 false
  let injury := fun total => MainRules.injury .crushing 0
    (MainRules.basicDamage (MainRules.Weapon.punch.damage 10) .crushing total)
  [(next 0, (1 - maximized - hit) / 2)] ++
    ((List.range 6).map fun face => (next (injury (face + 1)), hit / 12)) ++
    [(next (injury 6), maximized / 2), (duelIndex a b (1 - turn) true, 1/2)]

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

private theorem sum_weight (row : List (Fin n × ℚ)) (f : Fin n → ℝ) :
    ∑ v, (weight row v : ℝ) * f v = (row.map fun e => (e.2 : ℝ) * f e.1).sum := by
  induction row with
  | nil => simp [weight]
  | cons e rest ih =>
    simp only [weight, List.map_cons, List.sum_cons, Rat.cast_add, add_mul,
      Finset.sum_add_distrib] at *
    rw [ih]
    congr 1
    simp [apply_ite, ite_mul]

def Graph.chain (g : Graph n) (goal : Fin n → Bool) : MarkovChain (Fin n) Unit where
  initial := g.initial
  label _ := none
  transition s v := weight (g.rows s) v
  transition_nonneg s v := by
    apply Rat.cast_nonneg.mpr
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact g.nonneg s e he
    · exact le_rfl
  transition_sum s := by
    have h := sum_weight (g.rows s) (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h]
    have hh := congrArg (fun q : ℚ => (q : ℝ)) (g.normalized s)
    simpa [Function.comp_def] using hh
  defeat := {s | goal s = true}

theorem Graph.mem_defeat (g : Graph n) (goal : Fin n → Bool) (s : Fin n) :
    s ∈ (g.chain goal).defeat ↔ goal s = true := Iff.rfl

theorem Graph.transition (g : Graph n) (goal : Fin n → Bool) (s v : Fin n) :
    (g.chain goal).transition s v = (weight (g.rows s) v : ℝ) := rfl

theorem Graph.step_cast (g : Graph n) (goal : Fin n → Bool) (f : Fin n → ℚ) (s : Fin n) :
    (g.chain goal).step (fun v => (f v : ℝ)) s = (dot (g.rows s) f : ℝ) := by
  change (∑ v, (weight (g.rows s) v : ℝ) * (f v : ℝ)) = _
  rw [sum_weight]
  simp [dot, Function.comp_def]

/-- A finite distance witness requires only one positive edge towards an output.
Other edges may cycle, including indefinitely many failed attacks or defenses. -/
structure Paths (g : Graph n) where
  rank : Fin n → ℕ
  next : Fin n → Fin n
  progresses : ∀ s, g.terminal s = false →
    0 < weight (g.rows s) (next s) ∧ rank (next s) < rank s

theorem Paths.reaches (g : Graph n) (c : Paths g) (s : Fin n) :
    ∃ t, g.terminal t = true ∧ Relation.ReflTransGen (g.chain g.terminal).Edge s t := by
  have aux : ∀ k s, c.rank s = k →
      ∃ t, g.terminal t = true ∧ Relation.ReflTransGen (g.chain g.terminal).Edge s t := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s hk
      cases ht : g.terminal s with
      | true => exact ⟨s, ht, .refl⟩
      | false =>
        have h := c.progresses s ht
        obtain ⟨t, hterm, path⟩ := ih _ (by omega) (c.next s) rfl
        refine ⟨t, hterm, path.head ?_⟩
        change 0 < (weight (g.rows s) (c.next s) : ℝ)
        exact_mod_cast h.1
  exact aux _ s rfl

theorem Paths.terminates (g : Graph n) (c : Paths g) (s : Fin n) :
    (g.chain g.terminal).hInf s = 1 :=
  (g.chain g.terminal).hInf_eq_one_of_reachable_target (c.reaches g) s

private theorem harmonic_unique (M : MarkovChain (Fin n) Unit) (T : Set (Fin n))
    (reach : ∀ s, ∃ t ∈ T, Relation.ReflTransGen M.Edge s t)
    (absorbing : ∀ s ∈ T, ∀ v, M.Edge s v → v = s)
    (f g : Fin n → ℝ) (boundary : ∀ s ∈ T, f s = g s)
    (hf : ∀ s, s ∉ T → M.step f s = f s)
    (hg : ∀ s, s ∉ T → M.step g s = g s) : f = g := by
  have lower_bound (a b : Fin n → ℝ) (hb : ∀ s ∈ T, a s = b s)
      (ha : ∀ s, s ∉ T → M.step a s = a s)
      (hbb : ∀ s, s ∉ T → M.step b s = b s) : ∀ s, b s ≤ a s := by
    have : Nonempty (Fin n) := ⟨M.initial⟩
    obtain ⟨v₀, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun v => a v - b v)
      Finset.univ_nonempty
    have low (v : Fin n) : a v₀ - b v₀ ≤ a v - b v := hmin v (Finset.mem_univ v)
    have propagate (s v : Fin n) (hs : a s - b s = a v₀ - b v₀) (edge : M.Edge s v) :
        a v - b v = a v₀ - b v₀ := by
      by_cases ht : s ∈ T
      · simpa only [absorbing s ht v edge] using hs
      · have nonneg (u : Fin n) : 0 ≤ M.transition s u *
            ((a u - b u) - (a v₀ - b v₀)) :=
          mul_nonneg (M.transition_nonneg s u) (sub_nonneg.mpr (low u))
        have hz : ∑ u, M.transition s u * ((a u - b u) - (a v₀ - b v₀)) = 0 := by
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, ← Finset.sum_mul, M.transition_sum, one_mul, one_mul]
          change M.step a s - M.step b s - (a v₀ - b v₀) = 0
          rw [ha s ht, hbb s ht, hs, sub_self]
        have he := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => nonneg u)).mp hz v
          (Finset.mem_univ v)
        exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt edge))
    obtain ⟨t, ht, path⟩ := reach v₀
    have hv : a t - b t = a v₀ - b v₀ := by
      clear ht
      induction path with
      | refl => rfl
      | @tail u v path edge ih => exact propagate u v ih edge
    have hz : a v₀ - b v₀ = 0 := by rw [hb t ht, sub_self] at hv; exact hv.symm
    intro s
    have h := low s
    linarith
  funext s
  exact le_antisymm (lower_bound g f (fun s hs => (boundary s hs).symm) hg hf s)
    (lower_bound f g boundary hf hg s)

theorem Graph.terminal_h (g : Graph n) (goal : Fin n → Bool) (s : Fin n)
    (hs : g.terminal s = true) (k : ℕ) :
    (g.chain goal).h k s = if goal s then 1 else 0 := by
  induction k with
  | zero => simp only [MarkovChain.h_zero, Graph.mem_defeat]
  | succ k ih =>
    rw [MarkovChain.h_succ]
    simp only [Graph.mem_defeat, Graph.transition]
    rw [g.absorbing s hs]
    cases hg : goal s <;> simp [weight, apply_ite, ite_mul, ih, hg]

theorem Graph.terminal_hInf (g : Graph n) (goal : Fin n → Bool) (s : Fin n)
    (hs : g.terminal s = true) :
    (g.chain goal).hInf s = if goal s then 1 else 0 := by
  unfold MarkovChain.hInf
  simp only [g.terminal_h goal s hs]
  exact ciSup_const

/-- A proposed exact absorption probability for any selected output class. -/
structure Solution (g : Graph n) (goal : Fin n → Bool) where
  value : Fin n → ℚ
  goal_terminal : ∀ s, goal s = true → g.terminal s = true
  boundary : ∀ s, g.terminal s = true → value s = if goal s then 1 else 0
  harmonic : ∀ s, g.terminal s = false → dot (g.rows s) value = value s

/-- The proposed probabilities are proved equal to the existing hInf, not
accepted as an extra probabilistic assumption. -/
theorem Solution.exact (g : Graph n) (paths : Paths g) (goal : Fin n → Bool)
    (sol : Solution g goal) (s : Fin n) :
    (g.chain goal).hInf s = (sol.value s : ℝ) := by
  have h := harmonic_unique (g.chain goal) {v | g.terminal v = true}
    (paths.reaches g) (fun v hv w edge => by
      change 0 < (weight (g.rows v) w : ℝ) at edge
      rw [g.absorbing v hv] at edge
      by_contra hne
      simp [weight, Ne.symm hne] at edge)
    (g.chain goal).hInf (fun v => (sol.value v : ℝ))
    (fun v hv => by
      rw [g.terminal_hInf goal v hv, sol.boundary v hv]
      cases goal v <;> norm_num)
    (fun v hv => by
      apply Eq.symm
      apply (g.chain goal).hInf_step
      exact fun hg => hv (sol.goal_terminal v hg))
    (fun v hv => by
      rw [g.step_cast]
      rw [sol.harmonic v (Bool.eq_false_iff.mpr hv)])
  exact congrFun h s

/-- A checked dynamic-programming table. Supplying intermediate rows avoids
recomputing exponentially many paths inside the Lean kernel. -/
structure Horizon (g : Graph n) (goal : Fin n → Bool) (N : ℕ) where
  table : Fin (N + 1) → Fin n → ℚ
  zero : ∀ s, table ⟨0, by omega⟩ s = if goal s then 1 else 0
  step : ∀ k : Fin N, ∀ s,
    table ⟨k.val + 1, by omega⟩ s =
      if goal s then 1 else dot (g.rows s) (table ⟨k.val, by omega⟩)

theorem Horizon.correct (g : Graph n) (goal : Fin n → Bool) (N : ℕ)
    (c : Horizon g goal N) (k : Fin (N + 1)) (s : Fin n) :
    (g.chain goal).h k.val s = (c.table k s : ℝ) := by
  have aux : ∀ k (hk : k < N + 1) s,
      (g.chain goal).h k s = (c.table ⟨k, hk⟩ s : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro hk s
      rw [c.zero]
      simp only [MarkovChain.h_zero, Graph.mem_defeat]
      cases goal s <;> norm_num
    | succ k ih =>
      intro hk s
      have hs := c.step ⟨k, by omega⟩ s
      rw [hs, MarkovChain.h_succ]
      simp only [Graph.mem_defeat, Graph.transition]
      simp only [ih (by omega)]
      have hdot := g.step_cast goal (c.table ⟨k, by omega⟩) s
      change (∑ v, (weight (g.rows s) v : ℝ) * _) = _ at hdot
      cases goal s <;> simp [hdot]
  exact aux k.val k.isLt s

theorem Horizon.terminates (g : Graph n) (N : ℕ) (c : Horizon g g.terminal N)
    (last : c.table ⟨N, by omega⟩ g.initial = 1) :
    (g.chain g.terminal).hInf g.initial = 1 := by
  apply le_antisymm ((g.chain g.terminal).hInf_le_one _)
  have h := (g.chain g.terminal).h_le_hInf N g.initial
  rw [c.correct g g.terminal N ⟨N, by omega⟩, last] at h
  simpa using h

def Horizon.reference (g : Graph n) (N : ℕ) (c : Horizon g g.terminal N)
    (last : c.table ⟨N, by omega⟩ g.initial = 1) : ReferenceLaw.PhaseType (Fin n) Unit :=
  ⟨g.chain g.terminal, c.terminates g N last⟩

/-- Finite-prefix verification plus absorption covers ALL timestamps. This is
a theorem about the full distribution, not an assertion after eight samples. -/
theorem phaseType_fair (g : Graph n) (ref : Graph m) (N : ℕ)
    (a : Horizon g g.terminal N) (b : Horizon ref ref.terminal N)
    (lastA : a.table ⟨N, by omega⟩ g.initial = 1)
    (lastB : b.table ⟨N, by omega⟩ ref.initial = 1)
    (ε : ℝ≥0)
    (band : ∀ k, |(a.table k g.initial : ℝ) - (b.table k ref.initial : ℝ)| ≤ (ε : ℝ)) :
    (g.chain g.terminal).IsMarkovFairPhaseType g.initial (b.reference ref N lastB) ε := by
  rw [MarkovChain.isMarkovFairPhaseType_iff]
  intro k
  change |(g.chain g.terminal).h k g.initial - (ref.chain ref.terminal).h k ref.initial| ≤ _
  by_cases hk : k ≤ N
  · rw [a.correct g g.terminal N ⟨k, by omega⟩, b.correct ref ref.terminal N ⟨k, by omega⟩]
    exact band _
  · have doneA : (g.chain g.terminal).h N g.initial = 1 := by
      rw [a.correct g g.terminal N ⟨N, by omega⟩, lastA]; norm_num
    have doneB : (ref.chain ref.terminal).h N ref.initial = 1 := by
      rw [b.correct ref ref.terminal N ⟨N, by omega⟩, lastB]; norm_num
    have ha := (g.chain g.terminal).h_mono g.initial (show N ≤ k by omega)
    have hb := (ref.chain ref.terminal).h_mono ref.initial (show N ≤ k by omega)
    have ua := (g.chain g.terminal).h_le_one k g.initial
    have ub := (ref.chain ref.terminal).h_le_one k ref.initial
    dsimp only at ha hb
    rw [doneA] at ha
    rw [doneB] at hb
    have ea : (g.chain g.terminal).h k g.initial = 1 := le_antisymm ua ha
    have eb : (ref.chain ref.terminal).h k ref.initial = 1 := le_antisymm ub hb
    simp only [ea, eb, sub_self, abs_zero]
    exact ε.property

end
end MarkovRPG.Workshop
