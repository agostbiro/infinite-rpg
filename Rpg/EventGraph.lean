import Rpg.Spec

/-!
# No Short Loops

A loop is a path of Choices that comes back to the Scene where it started. Each Scene that an
Outcome can lead to counts as one step, also a roll branch that is not likely and the Scene after
a Fight is won. This file checks that every loop has at least 4 steps, so a Player who goes
round a loop sees at least 4 different Scenes before the first one comes back.

The main theorem is `Adventure.noShortLoops`: if `checkShortLoops` passes, every path of Choices
from a Scene back to the same Scene has 0 steps or at least 4 steps. Its statement uses `Leads`
from the spec, so a reader does not need to read the check to know what it means.
-/

namespace Rpg

/-- Every link in the Adventure: the pair (Scene, next Scene) for each Scene that a Choice leads
to. A roll gives two links, one for each branch. -/
def Adventure.links (a : Adventure) : List (SceneId × SceneId) :=
  a.scenes.flatMap fun s => s.choices.flatMap fun c => c.outcome.targets.map (s.id, ·)

/-- No loop of links has 1, 2 or 3 steps. For each link from `s` to `t`: `t` is not `s`, no
link goes from `t` back to `s`, and no Scene `u` has links from `t` to `u` and from `u` to `s`. -/
def Adventure.NoShortLoops (a : Adventure) : Prop :=
  ∀ e ∈ a.links,
    e.1 ≠ e.2 ∧
    (e.2, e.1) ∉ a.links ∧
    ∀ f ∈ a.links, e.2 = f.1 → (f.2, e.1) ∉ a.links

instance (a : Adventure) : Decidable a.NoShortLoops := by
  unfold Adventure.NoShortLoops
  infer_instance

/-- The check for short loops. It allows loops of 4 or more steps. -/
def Adventure.checkShortLoops (a : Adventure) : Bool := decide a.NoShortLoops

/-- If the check passes, the Adventure has no short loops. -/
theorem Adventure.checkShortLoops_sound (a : Adventure)
    -- The check passes.
    (h : a.checkShortLoops = true) :
    a.NoShortLoops :=
  of_decide_eq_true h

/-- If a Choice in Scene `s` leads to Scene `t`, then `(s, t)` is a link. -/
theorem Adventure.mem_links_of_leads {a : Adventure} {s t : SceneId}
    -- A Choice in `s` leads to `t`.
    (h : Leads a s t) :
    (s, t) ∈ a.links := by
  obtain ⟨sc, hsc, hid, ch, hch, ht⟩ := h
  simp only [Adventure.links, List.mem_flatMap, List.mem_map]
  exact ⟨sc, hsc, ch, hch, t, ht, by rw [hid]⟩

/-- `ChoicePath a s t n`: following `n` Choices leads from Scene `s` to Scene `t`. -/
inductive ChoicePath (a : Adventure) : SceneId → SceneId → Nat → Prop where
  /-- A path of 0 steps stays in its Scene. -/
  | stay (s : SceneId) : ChoicePath a s s 0
  /-- A Choice in `s` that leads to `t`, then a path from `t`, is a path from `s` with one more step. -/
  | step {s t u : SceneId} {n : Nat} : Leads a s t → ChoicePath a t u n → ChoicePath a s u (n + 1)

/-- If the check passes, every loop has at least 4 steps: a path of Choices from a Scene back to
the same Scene, with at least one step, has 4 steps or more. -/
theorem Adventure.noShortLoops (a : Adventure) {s : SceneId} {n : Nat}
    -- The short-loop check passes.
    (checked : a.checkShortLoops = true)
    -- Following `n` Choices leads from `s` back to `s`.
    (loop : ChoicePath a s s n)
    -- The path has at least one step.
    (positive : 0 < n) :
    4 ≤ n := by
  have safe := a.checkShortLoops_sound checked
  cases loop with
  -- A path of 0 steps contradicts `positive`.
  | stay => omega
  | step first tail =>
    have l1 := Adventure.mem_links_of_leads first
    cases tail with
    -- A loop of 1 step: the first link goes from `s` to `s`.
    | stay => exact False.elim ((safe _ l1).1 rfl)
    | step second rest =>
      have l2 := Adventure.mem_links_of_leads second
      cases rest with
      -- A loop of 2 steps: the second link goes back to `s`.
      | stay => exact False.elim ((safe _ l1).2.1 l2)
      | step third last =>
        have l3 := Adventure.mem_links_of_leads third
        cases last with
        -- A loop of 3 steps: the third link goes back to `s`.
        | stay => exact False.elim ((safe _ l1).2.2 _ l2 rfl l3)
        -- A path of 4 or more steps.
        | step _ _ => omega

/-! ## Errors for the DM -/

/-- The short loop that starts with the link `e`, as its list of Scenes, or `none` if there is
no such loop. It gives a result exactly when `e` breaks `NoShortLoops`. -/
def Adventure.shortLoopAt (a : Adventure) (e : SceneId × SceneId) : Option (List SceneId) :=
  if e.1 = e.2 then some [e.1]
  else if (e.2, e.1) ∈ a.links then some [e.1, e.2]
  else match a.links.find? (fun f => f.1 == e.2 && (f.2, e.1) ∈ a.links) with
    | some f => some [e.1, e.2, f.2]
    | none => none

/-- Turn a loop so that its smallest Scene number comes first. Then each loop has one form. -/
def loopFromSmallest (loop : List SceneId) : List SceneId :=
  let low := loop.foldl min (loop.headD 0)
  let i := loop.idxOf low
  loop.drop i ++ loop.take i

/-- The error for one short loop, such as "the loop Scene 2 -> Scene 5 -> Scene 2 has 2
steps". -/
def shortLoopError (loop : List SceneId) : String :=
  let scenes := (loop ++ loop.take 1).map (s!"Scene {·}")
  let steps := if loop.length = 1 then "1 step" else s!"{loop.length} steps"
  s!"the loop {" -> ".intercalate scenes} has {steps}, but a loop needs at least 4 steps: make it longer or remove it"

/-- One error for each short loop in the Adventure, with its Scene numbers. -/
def Adventure.shortLoopErrors (a : Adventure) : List String :=
  ((a.links.filterMap a.shortLoopAt).map loopFromSmallest).eraseDups.map shortLoopError

/-! ## Examples -/

/-- A small Adventure with one Scene per link. Each Scene has one Choice that goes to the next
Scene of its link. -/
def shortLoopExample (links : List (Nat × Nat)) : Adventure :=
  { title := "Loop check", start := 0, scenes := links.map fun (s, t) =>
      { id := s, title := "Scene", text := "Example", choices := [{ text := "Go on", outcome := .goto t }] } }

/-- A good example: a loop of 4 steps passes the check. -/
example : (shortLoopExample [(0, 1), (1, 2), (2, 3), (3, 0)]).NoShortLoops := by decide

-- Rejected examples: loops of 1, 2 and 3 steps fail the check.
example : ¬ (shortLoopExample [(0, 0)]).NoShortLoops := by decide
example : ¬ (shortLoopExample [(0, 1), (1, 0)]).NoShortLoops := by decide
example : ¬ (shortLoopExample [(0, 1), (1, 2), (2, 0)]).NoShortLoops := by decide

/-- The main theorem holds on a real loop of 4 steps, with every premise met. -/
example : 4 ≤ 4 :=
  (shortLoopExample [(0, 1), (1, 2), (2, 3), (3, 0)]).noShortLoops (by decide)
    (.step (t := 1) (by unfold Leads; decide)
    (.step (t := 2) (by unfold Leads; decide)
    (.step (t := 3) (by unfold Leads; decide)
    (.step (t := 0) (by unfold Leads; decide)
    (.stay 0))))) (by decide)

-- The errors name each short loop once, with its smallest Scene first.
#guard (shortLoopExample [(0, 1), (1, 2), (2, 3), (3, 0)]).shortLoopErrors == []
#guard (shortLoopExample [(4, 4)]).shortLoopErrors ==
  ["the loop Scene 4 -> Scene 4 has 1 step, but a loop needs at least 4 steps: make it longer or remove it"]
#guard (shortLoopExample [(5, 2), (2, 5)]).shortLoopErrors ==
  ["the loop Scene 2 -> Scene 5 -> Scene 2 has 2 steps, but a loop needs at least 4 steps: make it longer or remove it"]
#guard (shortLoopExample [(3, 1), (1, 2), (2, 3)]).shortLoopErrors ==
  ["the loop Scene 1 -> Scene 2 -> Scene 3 -> Scene 1 has 3 steps, but a loop needs at least 4 steps: make it longer or remove it"]
-- A roll counts both branches, also a branch back to the same Scene.
#guard ({ title := "Roll", start := 0, scenes := [
    { id := 0, title := "A", text := "", choices := [{ text := "Try", outcome := .roll (.attribute .dx) 0 1 0 }] },
    { id := 1, title := "B", text := "", choices := [] }] } : Adventure).shortLoopErrors.length == 1

end Rpg
