import MarkovRPGCharacters

/-!
# Scenes as a spatial realization of adventure events

A scene refers to existing items and characters; it does not copy their mechanics.
`ν e s` is Boolean event membership. Active scenes are derived from the current
event. HP variants of an event therefore have the same location.

The scene graph is a directed projection of positive-probability adventure edges,
not a second Markov chain: probabilities cannot in general be aggregated by scene.
An internal transition remains a game transition but creates no travel edge.
Terminal outputs may have no physical location. Fairness and noSmallCycles still
apply to the adventure graph, not to this spatial projection.
-/

namespace MarkovRPG.Scenes

/-- Enumerate sparse outgoing rows once, preserving exactly their support. -/
def edgesFromRows (n : Nat) (targets : Fin n → List (Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (targets u).map fun v => (u,v)

theorem mem_edgesFromRows (n : Nat) (targets : Fin n → List (Fin n)) (u v : Fin n) :
    (u,v) ∈ edgesFromRows n targets ↔ v ∈ targets u := by
  simp [edgesFromRows, List.mem_flatMap]

/-- Dense support adapter retained for already exported certificates.
New certificates use sparse outgoing rows directly. -/
def enumerateEdges (n : Nat) (edge : Fin n → Fin n → Bool) : List (Fin n × Fin n) :=
  edgesFromRows n (fun u => (List.finRange n).filter fun v => edge u v)

theorem mem_enumerateEdges (n : Nat) (edge : Fin n → Fin n → Bool) (u v : Fin n) :
    (u,v) ∈ enumerateEdges n edge ↔ edge u v = true := by
  simp [enumerateEdges, mem_edgesFromRows]

/-- Compute only actual travel edges, in linear time in the supplied edge list.
Duplicate witnesses are harmless and can be deduplicated by the renderer. -/
def projectPair {V S : Type*} [DecidableEq S] (location : V → Option S)
    (e : V × V) : List (S × S) :=
  match location e.1, location e.2 with
  | some s, some t => if s = t then [] else [(s,t)]
  | _, _ => []

theorem mem_projectPair {V S : Type*} [DecidableEq S] (location : V → Option S)
    (e : V × V) (s t : S) :
    (s,t) ∈ projectPair location e ↔
      s ≠ t ∧ location e.1 = some s ∧ location e.2 = some t := by
  cases h₁ : location e.1 <;> cases h₂ : location e.2 <;>
    simp [projectPair, h₁, h₂]
  aesop

def projectEdges {V S : Type*} [DecidableEq S] (location : V → Option S)
    (edges : List (V × V)) : List (S × S) := edges.flatMap (projectPair location)

theorem mem_projectEdges {V S : Type*} [DecidableEq S] (location : V → Option S)
    (edges : List (V × V)) (s t : S) :
    (s,t) ∈ projectEdges location edges ↔
      s ≠ t ∧ ∃ v w, (v,w) ∈ edges ∧ location v = some s ∧ location w = some t := by
  simp only [projectEdges, List.mem_flatMap, mem_projectPair]
  constructor
  · rintro ⟨⟨v,w⟩,he,h,hs,ht⟩
    exact ⟨h,v,w,he,hs,ht⟩
  · rintro ⟨h,v,w,he,hs,ht⟩
    exact ⟨(v,w),he,h,hs,ht⟩

/-- References to the existing item and character definitions. A scene's contents
describe presence, not additional enabled actions. The moving player is separate. -/
structure Scene where
  objects : Finset ItemId := ∅
  characters : Finset CharacterId := ∅

def Scene.WellFormed (s : Scene) (items : ItemId → Option Item)
    (people : CharacterId → Option Character) : Prop :=
  (∀ i ∈ s.objects, ∃ item, items i = some item ∧ item.id = i) ∧
  (∀ c ∈ s.characters, ∃ character, people c = some character ∧ character.id = c)

/-- A total spatial assignment for playable events, with unlocated outputs. -/
structure Layout (Event Location : Type*) where
  playable : Event → Prop
  ν : Event → Location → Bool
  unique : ∀ e, playable e → ∃! s, ν e s = true
  outside : ∀ e, ¬ playable e → ∀ s, ν e s = false

namespace Layout

variable {E S V A : Type*}

/-- Efficient representation: store one optional location, derive membership.
The executable generator uses this constructor rather than storing a matrix. -/
def ofLocation [DecidableEq S] (location : E → Option S) : Layout E S where
  playable e := (location e).isSome = true
  ν e s := decide (location e = some s)
  unique e h := by
    cases he : location e with
    | none => simp [he] at h
    | some s =>
      refine ⟨s, by simp, ?_⟩
      intro y hy
      exact (show s = y by simpa [he] using hy).symm
  outside e h s := by
    cases he : location e with
    | none => simp
    | some x => simp [he] at h

def Active (L : Layout E S) (event : V → E) (v : V) (s : S) : Prop :=
  L.ν (event v) s = true

theorem unique_active (L : Layout E S) (event : V → E) (v : V)
    (h : L.playable (event v)) : ∃! s, L.Active event v s := L.unique _ h

theorem no_active_output (L : Layout E S) (event : V → E) (v : V)
    (h : ¬ L.playable (event v)) : ∀ s, ¬ L.Active event v s := by
  intro s
  simp [Active, L.outside _ h]

theorem variants_same_scene (L : Layout E S) (event : V → E)
    {v w : V} (h : event v = event w) (s : S) :
    L.Active event v s ↔ L.Active event w s := by simp [Active, h]

/-- The relation is recomputed from the supplied game graph after every edit. -/
def Edge (L : Layout E S) (event : V → E) (edge : V → V → Prop) (s t : S) : Prop :=
  s ≠ t ∧ ∃ v w, edge v w ∧ L.Active event v s ∧ L.Active event w t

theorem edge_has_game_witness (L : Layout E S) (event : V → E)
    (edge : V → V → Prop) {s t : S} (h : L.Edge event edge s t) :
    ∃ v w, edge v w ∧ L.Active event v s ∧ L.Active event w t := h.2

theorem game_step_projects (L : Layout E S) (event : V → E)
    (edge : V → V → Prop) {v w : V} {s t : S} (h : edge v w)
    (hs : L.Active event v s) (ht : L.Active event w t) :
    s = t ∨ L.Edge event edge s t := by
  by_cases heq : s = t
  · exact Or.inl heq
  · exact Or.inr ⟨heq, v, w, h, hs, ht⟩

theorem no_travel_loop (L : Layout E S) (event : V → E)
    (edge : V → V → Prop) (s : S) : ¬ L.Edge event edge s s := fun h => h.1 rfl

/-- The spatial interface retains the exact current-state action filter.
Another event in the same room cannot contribute its actions. -/
def Enabled (L : Layout E S) (event : V → E) (source : A → V)
    (current : V) (s : S) (a : A) : Prop :=
  L.Active event current s ∧ source a = current

theorem enabled_iff_current_action (L : Layout E S) (event : V → E)
    (source : A → V) {current : V} {s : S} (h : L.Active event current s) (a : A) :
    L.Enabled event source current s a ↔ source a = current := by
  simp [Enabled, h]

theorem other_event_disabled (L : Layout E S) (event : V → E)
    (source : A → V) (current : V) (s : S) (a : A) (h : source a ≠ current) :
    ¬ L.Enabled event source current s a := fun ha => h ha.2

/-- Replacing edges can add and remove scene connections; equality of the newly
derived relation is the contract, not monotonic retention of old connections. -/
def Realizes (L : Layout E S) (event : V → E) (edge : V → V → Prop)
    (renderEdge : S → S → Prop) : Prop :=
  ∀ s t, renderEdge s t ↔ L.Edge event edge s t

theorem realizes_after_update (L : Layout E S) (event : V → E)
    (newEdge : V → V → Prop) : L.Realizes event newEdge (L.Edge event newEdge) :=
  fun _ _ => Iff.rfl

end Layout
end MarkovRPG.Scenes
