import MarkovRPGCombatEvents
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Additional properties of adventure graphs

These are generic predicates, not changes to the adventure generator or combat
rules. Combat is already collapsed to one event by `Combat.WorldEvent.law`.

* Only the cycle-checking view forgets direction and identifies opposite arrows
  with a single segment. The game's actions, arrows, and probabilities are never
  changed. A cycle is a simple cycle, not a walk which traverses
  one segment and immediately returns along it. Triangles are forbidden; squares
  and longer cycles are permitted. Nonterminal self-loops are forbidden separately.
* A decision is one available action at one source vertex. Its outcome PMF is
  examined BEFORE a player strategy mixes different actions. Only positive-mass
  destinations count. Duplicate die faces leading to the same vertex count once.
* Counts are uniform structural counts, not visit-frequency-weighted statistics.
  Terminal bookkeeping actions are excluded. All other supplied actions count,
  including actions at unreachable vertices if the supplied graph contains them.
* The bound is inclusive and rational: deterministicCount <= x * decisionCount,
  with 0 <= x <= 1. An empty decision set has fraction zero.

No new graph or probability model is introduced: the predicates consume existing
edge relations and PMFs. `HasAdditionalProperties` derives both checks from the
same action laws. State variables relevant to future play remain in the vertices.
-/

noncomputable section
open Classical
open scoped BigOperators ENNReal

namespace MarkovRPG.AdventureProperties

section Cycles

variable {V : Type*}

/-- Direction is forgotten; reciprocal arrows give one segment, not a 2-cycle.
Self-loops are handled explicitly by `NoSmallCycles`, since SimpleGraph omits them. -/
def undirected (edge : V → V → Prop) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (edge u v ∨ edge v u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A finite, local characterization of undirected girth at least four,
with an additional explicit prohibition on self-loops. -/
def NoSmallCycles (edge : V → V → Prop) : Prop :=
  (∀ v, ¬ edge v v) ∧
  ∀ a b c, ¬ ((undirected edge).Adj a b ∧
    (undirected edge).Adj b c ∧ (undirected edge).Adj c a)

/-- Sparse certificate for the same property. Only pairs of actual neighbors
need examination; the full vertex cube need not be reduced by the kernel. -/
theorem noSmallCycles_of_neighbors (edge : V → V → Prop) (neighbors : V → List V)
    (exact_neighbors : ∀ a b, (undirected edge).Adj a b ↔ b ∈ neighbors a)
    (no_loops : ∀ v, ¬ edge v v)
    (no_triangles : ∀ a, ∀ b ∈ neighbors a, ∀ c ∈ neighbors b, a ∉ neighbors c) :
    NoSmallCycles edge := by
  refine ⟨no_loops, ?_⟩
  intro a b c h
  exact no_triangles a b ((exact_neighbors a b).mp h.1)
    c ((exact_neighbors b c).mp h.2.1) ((exact_neighbors c a).mp h.2.2)

/-- The triangle test is exactly the condition on lengths of simple cycles. -/
theorem no_triangles_iff_cycle_length (G : SimpleGraph V) :
    (∀ a b c, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) ↔
    ∀ a (w : G.Walk a a), w.IsCycle → 4 ≤ w.length := by
  constructor
  · intro h a w hw
    by_contra hn
    have hthree := hw.three_le_length
    have heq : w.length = 3 := by omega
    obtain ⟨s, hs⟩ := G.is3Clique_iff_exists_cycle_length_three.mpr ⟨a, w, hw, heq⟩
    obtain ⟨u, v, z, huv, huz, hvz, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact h u v z ⟨huv, hvz, huz.symm⟩
  · intro h a b c ⟨hab, hbc, hca⟩
    have hc : G.IsNClique 3 {a, b, c} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩
    obtain ⟨u, w, hw, hlen⟩ := G.is3Clique_iff_exists_cycle_length_three.mp ⟨_, hc⟩
    have := h u w hw
    omega

theorem noSmallCycles_iff (edge : V → V → Prop) :
    NoSmallCycles edge ↔ (∀ v, ¬ edge v v) ∧
      ∀ a (w : (undirected edge).Walk a a), w.IsCycle → 4 ≤ w.length := by
  unfold NoSmallCycles
  rw [no_triangles_iff_cycle_length]

theorem NoSmallCycles.cycle_length {edge : V → V → Prop} (h : NoSmallCycles edge)
    {a : V} (w : (undirected edge).Walk a a) (hw : w.IsCycle) : 4 ≤ w.length :=
  (noSmallCycles_iff edge).mp h |>.2 a w hw

/-- Acyclic graphs have infinite extended girth and are accepted as well. -/
theorem NoSmallCycles.girth {edge : V → V → Prop} (h : NoSmallCycles edge) :
    4 ≤ (undirected edge).egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  exact_mod_cast h.cycle_length w hw

/-- Remove only terminal self-loops from the cycle-checking view. All edges
between distinct vertices remain, including edges incident to Win/Lose. -/
def eventEdges (terminal : Set V) (edge : V → V → Prop) (s v : V) : Prop :=
  (s ≠ v ∨ s ∉ terminal) ∧ edge s v

@[simp] theorem eventEdges_of_ne (terminal : Set V) (edge : V → V → Prop)
    {s v : V} (hne : s ≠ v) : eventEdges terminal edge s v ↔ edge s v := by
  simp [eventEdges, hne]

@[simp] theorem eventEdges_terminal_loop (terminal : Set V) (edge : V → V → Prop)
    {s : V} (hs : s ∈ terminal) : ¬ eventEdges terminal edge s s := by
  simp [eventEdges, hs]

/-- The existing chain is inspected without modifying its transition matrix. -/
def chainEdges [Fintype V] {Label : Type*} (M : MarkovChain V Label)
    (terminal : Set V) : V → V → Prop := eventEdges terminal M.Edge

@[simp] theorem chainEdges_terminal_loop [Fintype V] {Label : Type*}
    (M : MarkovChain V Label) (terminal : Set V) {s : V} (hs : s ∈ terminal) :
    ¬ chainEdges M terminal s s := by simp [chainEdges, hs]

end Cycles

section Decisions

variable {V D : Type*} [Fintype V]

/-- Distinct destinations with strictly positive probability. -/
def outputs (law : PMF V) : Finset V := Finset.univ.filter fun v => v ∈ law.support

@[simp] theorem mem_outputs (law : PMF V) (v : V) :
    v ∈ outputs law ↔ v ∈ law.support := by simp [outputs]

theorem outputs_nonempty (law : PMF V) : (outputs law).Nonempty := by
  obtain ⟨v, hv⟩ := law.support_nonempty
  exact ⟨v, (mem_outputs law v).mpr hv⟩

def IsDeterministic (law : PMF V) : Prop := (outputs law).card = 1

def IsRandom (law : PMF V) : Prop := 2 ≤ (outputs law).card

/-- Exactly one possible output is equivalent to one output of probability one. -/
theorem deterministic_iff_probability_one (law : PMF V) :
    IsDeterministic law ↔ ∃ v, law v = 1 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
    refine ⟨v, (law.apply_eq_one_iff v).mpr ?_⟩
    ext u
    simpa [hv] using (mem_outputs law u).symm
  · rintro ⟨v, hv⟩
    have hs := (law.apply_eq_one_iff v).mp hv
    have ho : outputs law = {v} := by ext u; simp [hs]
    simp [IsDeterministic, ho]

@[simp] theorem pure_deterministic (v : V) : IsDeterministic (PMF.pure v) :=
  (deterministic_iff_probability_one _).mpr ⟨v, by simp⟩

/-- Normalization rules out an empty outcome support, so there is no third case. -/
theorem random_iff_not_deterministic (law : PMF V) :
    IsRandom law ↔ ¬ IsDeterministic law := by
  have hpos := Finset.card_pos.mpr (outputs_nonempty law)
  unfold IsRandom IsDeterministic
  omega

theorem random_has_two_outputs {law : PMF V} (h : IsRandom law) :
    ∃ u v, u ≠ v ∧ 0 < law u ∧ 0 < law v := by
  obtain ⟨u, v, hu, hv, hne⟩ := Finset.one_lt_card_iff.mp (show 1 < (outputs law).card by exact h)
  exact ⟨u, v, hne, (law.apply_pos_iff u).mpr ((mem_outputs law u).mp hu),
    (law.apply_pos_iff v).mpr ((mem_outputs law v).mp hv)⟩

/-- A genuine random decision admits a nontrivial binary success event:
one output is designated success, and its complement is failure. No assertion
about the narrative meaning or the quality of that success event is made. -/
theorem random_has_success_probability {law : PMF V} (h : IsRandom law) :
    ∃ v, 0 < law v ∧ law v < 1 := by
  obtain ⟨u, v, hne, hu, hv⟩ := random_has_two_outputs h
  refine ⟨u, hu, ?_⟩
  have hlt : law u < 1 := by
    have hle : law u ≤ 1 := law.coe_le_one u
    have hnot : law u ≠ 1 := by
      intro hone
      have hdet := (deterministic_iff_probability_one law).mpr ⟨u, hone⟩
      exact (random_iff_not_deterministic law).mp h hdet
    exact lt_of_le_of_ne hle hnot
  exact hlt

def deterministicDecisions (decisions : Finset D) (law : D → PMF V) : Finset D :=
  decisions.filter fun d => IsDeterministic (law d)

def randomDecisions (decisions : Finset D) (law : D → PMF V) : Finset D :=
  decisions.filter fun d => IsRandom (law d)

/-- This fraction is defined to be zero when there are no counted decisions. -/
def deterministicFraction (decisions : Finset D) (law : D → PMF V) : ℚ :=
  (deterministicDecisions decisions law).card / (decisions.card : ℚ)

/-- Multiplication avoids division by zero and is suitable for exact checking. -/
def HasDeterministicDecisionBound (decisions : Finset D) (law : D → PMF V) (x : ℚ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ (deterministicDecisions decisions law).card ≤ x * (decisions.card : ℚ)

theorem decision_counts_partition (decisions : Finset D) (law : D → PMF V) :
    (deterministicDecisions decisions law).card + (randomDecisions decisions law).card =
      decisions.card := by
  simp only [deterministicDecisions, randomDecisions, random_iff_not_deterministic]
  exact Finset.card_filter_add_card_filter_not _

/-- At most x deterministic decisions means at least 1-x random decisions. -/
theorem deterministicBound_iff_randomLowerBound (decisions : Finset D)
    (law : D → PMF V) (x : ℚ) :
    HasDeterministicDecisionBound decisions law x ↔
      0 ≤ x ∧ x ≤ 1 ∧ (1-x) * (decisions.card : ℚ) ≤ (randomDecisions decisions law).card := by
  have hp : ((deterministicDecisions decisions law).card : ℚ) +
      (randomDecisions decisions law).card = decisions.card := by
    exact_mod_cast decision_counts_partition decisions law
  unfold HasDeterministicDecisionBound
  constructor <;> rintro ⟨h0, h1, hb⟩ <;> refine ⟨h0, h1, ?_⟩ <;> nlinarith

theorem deterministicBound_iff_fraction (decisions : Finset D)
    (law : D → PMF V) (x : ℚ) :
    HasDeterministicDecisionBound decisions law x ↔
      0 ≤ x ∧ x ≤ 1 ∧ deterministicFraction decisions law ≤ x := by
  by_cases hempty : decisions = ∅
  · simp [hempty, HasDeterministicDecisionBound, deterministicFraction, deterministicDecisions]
    exact fun h0 _ => h0
  · have hp : (0 : ℚ) < decisions.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    simp only [HasDeterministicDecisionBound, deterministicFraction, div_le_iff₀ hp]

/-- Source/action pairs, not averaged Markov rows, are the decision indices.
Each distinct enabled action must occur exactly once in D. -/
def liveDecisions [Fintype D] (source : D → V) (terminal : Set V) : Finset D :=
  Finset.univ.filter fun d => source d ∉ terminal

/-- Edges are derived from the same laws used by the proportion property. -/
def decisionEdges (decisions : Finset D) (source : D → V) (law : D → PMF V)
    (u v : V) : Prop := ∃ d ∈ decisions, source d = u ∧ v ∈ (law d).support

/-- The two requested properties, independent of any particular adventure. -/
def HasAdditionalProperties [Fintype D] (source : D → V) (terminal : Set V)
    (law : D → PMF V) (x : ℚ) : Prop :=
  NoSmallCycles (eventEdges terminal (decisionEdges Finset.univ source law)) ∧
    HasDeterministicDecisionBound (liveDecisions source terminal) law x

/-- Existing ordinary events and collapsed combats can supply the action laws
directly; their internal combat vertices do not enter the adventure cycle check. -/
def EventProperties [Fintype D] {r : Combat.Rules} (source : D → V) (terminal : Set V)
    (events : D → Combat.WorldEvent r V) (x : ℚ) : Prop :=
  HasAdditionalProperties source terminal (fun d => (events d).law) x

end Decisions

end MarkovRPG.AdventureProperties
