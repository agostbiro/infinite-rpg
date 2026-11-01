import Rpg.Adventure

/-! Event edges are the targets of the actual story outcomes, including both roll results.
The restriction concerns scene transitions, not walking paths or combat rounds. -/
namespace Rpg

/-- All directed event edges, including edges of outcomes with very small probability. -/
def Adventure.eventEdges (a : Adventure) : List (SceneId × SceneId) :=
  a.scenes.flatMap fun s => s.choices.flatMap fun c => c.outcome.targets.map (s.id, ·)

/-- No directed event cycle has one, two or three edges. -/
def Adventure.NoShortCycles (a : Adventure) : Prop :=
  ∀ e ∈ a.eventEdges, e.1 ≠ e.2 ∧ (e.2, e.1) ∉ a.eventEdges ∧
    ∀ f ∈ a.eventEdges, e.2 = f.1 → (f.2, e.1) ∉ a.eventEdges

instance (a : Adventure) : Decidable a.NoShortCycles := by
  unfold Adventure.NoShortCycles
  infer_instance

/-- An executable check of the event graph; it allows cycles of four or more edges. -/
def Adventure.checkEventCycles (a : Adventure) : Bool := decide a.NoShortCycles

/-- The executable check proves the stated restriction on the actual adventure edges. -/
theorem Adventure.checkEventCycles_sound (a : Adventure)
    (h : a.checkEventCycles = true) : a.NoShortCycles := by
  exact of_decide_eq_true h

/-- A walk counts scene transitions, independently of the physical distance walked. -/
inductive EventWalk (a : Adventure) : SceneId → SceneId → Nat → Prop where
  | nil (s) : EventWalk a s s 0
  | step {s t u n} : (s, t) ∈ a.eventEdges → EventWalk a t u n → EventWalk a s u (n+1)

/-- Every nonempty closed event walk in a checked graph has at least four edges. -/
theorem Adventure.«non-cyclic» (a : Adventure)
    (checked : a.checkEventCycles = true)
    (walk : EventWalk a s s n)
    (positive : 0 < n) : 4 ≤ n := by
  have safe := a.checkEventCycles_sound checked
  cases walk with
  | nil => omega
  | step first tail =>
    cases tail with
    | nil => exact False.elim ((safe _ first).1 rfl)
    | step second rest =>
      cases rest with
      | nil => exact False.elim ((safe _ first).2.1 second)
      | step third last =>
        cases last with
        | nil => exact False.elim ((safe _ first).2.2 _ second rfl third)
        | step _ _ => omega

/-- Actionable diagnostics for generated story graphs. -/
def Adventure.eventCycleErrors (a : Adventure) : List String :=
  a.eventEdges.eraseDups.filterMap fun (s, t) =>
    if s == t then some s!"graph: Scene {s} has a self-loop; event cycles need at least 4 edges"
    else if a.eventEdges.contains (t, s) then
      some s!"graph: Scenes {s} and {t} form a 2-edge cycle; use at least 4 distinct events"
    else match a.eventEdges.find? (fun (v,w) => v == t && a.eventEdges.contains (w,s)) with
      | some (_,u) => some s!"graph: Scenes {s}, {t}, {u} form a 3-edge cycle; use at least 4 distinct events"
      | none => none

/-- A small graph used to exercise the cycle specification. -/
def eventCycleExample (targets : List (Nat × Nat)) : Adventure :=
  { title := "Cycle check", start := 0, scenes := targets.map fun (s,t) =>
      { id := s, title := "Event", text := "Example", choices := [{ text := "Continue", outcome := .goto t }] } }

example : (eventCycleExample [(0,1),(1,2),(2,3),(3,0)]).NoShortCycles := by decide
example : ¬ (eventCycleExample [(0,0)]).NoShortCycles := by decide
example : ¬ (eventCycleExample [(0,1),(1,0)]).NoShortCycles := by decide
example : ¬ (eventCycleExample [(0,1),(1,2),(2,0)]).NoShortCycles := by decide
example : 4 ≤ 4 :=
  (eventCycleExample [(0,1),(1,2),(2,3),(3,0)]).«non-cyclic» (by decide)
    (.step (t := 1) (by decide) (.step (t := 2) (by decide)
      (.step (t := 3) (by decide) (.step (t := 0) (by decide) (.nil 0))))) (by decide)

end Rpg
