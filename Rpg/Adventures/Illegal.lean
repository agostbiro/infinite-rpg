import Rpg.Adventures.Lighthouse

/-!
# Illegal Adventures

Each Adventure here breaks one rule, the way a cheating DM might.
For each one we show two things:
the spec rejects it (`¬ LegalAdventure`), and the checker reports an error.
Each spec proof picks out the rule that the cheat breaks and shows by `decide` that the rule fails.
-/

namespace Rpg

/-- A small Adventure around one Choice. The Choice leads from Scene 0, and Scene 1 is an Ending. -/
def oneChoice (title : String) (o : Outcome) : Adventure where
  title := title
  start := 0
  scenes := [
    { id := 0, title := "Start", text := "", choices := [{ text := "Go", outcome := o }] },
    { id := 1, title := "End", text := "", choices := [] } ]

/-- Cheat 1: a goblin with ST 40. -/
def giantGoblin : Being where
  name := "Goblin"
  st := 40
  dx := 10
  iq := 8
  ht := 10
  skills := []
  weapon := .punch
  armor := .none

/-- An Adventure with an ST 40 goblin. -/
def cheatGiant : Adventure := oneChoice "Giant goblin" (.fight [giantGoblin] 1)

example : ¬ LegalAdventure mara cheatGiant := fun h => absurd h.2.2.2.1 (by decide)
example : check mara cheatGiant ≠ [] := by decide

/-- Cheat 2: a Choice that leads to a Scene that does not exist. -/
def cheatBrokenLink : Adventure := oneChoice "Broken link" (.goto 99)

example : ¬ LegalAdventure mara cheatBrokenLink := fun h => absurd h.2.2.2.1 (by decide)
example : check mara cheatBrokenLink ≠ [] := by decide

/-- Cheat 3: a lock at +15, far beyond the limit of +10. -/
def cheatEasyLock : Adventure := oneChoice "Easy lock" (.roll (.skill .lockpicking) 15 1 1)

example : ¬ LegalAdventure mara cheatEasyLock := fun h => absurd h.2.2.2.1 (by decide)
example : check mara cheatEasyLock ≠ [] := by decide

/-- A stone sentinel: DR 12 and too weak to hurt anyone. Neither side can win. -/
def stoneSentinel : Being where
  name := "Stone Sentinel"
  st := 3
  dx := 10
  iq := 10
  ht := 10
  skills := []
  weapon := .punch
  armor := .none
  naturalDR := 12

/-- Cheat 4: a Fight that can never end. -/
def cheatEndless : Adventure := oneChoice "Endless fight" (.fight [stoneSentinel] 1)

example : ¬ LegalAdventure mara cheatEndless := fun h => absurd h.2.2.2.1 (by decide)
example : check mara cheatEndless ≠ [] := by decide

/-- Cheat 5: no Ending, so the Adventure goes on forever. -/
def cheatNoEnding : Adventure where
  title := "No ending"
  start := 0
  scenes := [{ id := 0, title := "Loop", text := "", choices := [{ text := "Again", outcome := .goto 0 }] }]

example : ¬ LegalAdventure mara cheatNoEnding := fun h => absurd h.2.2.1 (by decide)
example : check mara cheatNoEnding ≠ [] := by decide

/-- Cheat 6: an Ending exists, but no Choice leads to it. The Player loops forever. -/
def cheatHiddenEnding : Adventure where
  title := "Hidden ending"
  start := 0
  scenes := [
    { id := 0, title := "Loop", text := "", choices := [{ text := "Again", outcome := .goto 0 }] },
    { id := 1, title := "Hidden End", text := "", choices := [] } ]

/-- In the hidden-ending Adventure, only Scene 0 can be reached. -/
theorem hiddenEnding_only_start {x : SceneId}
    (h : Reachable cheatHiddenEnding x) : x = 0 := by
  induction h with
  -- The start Scene is Scene 0.
  | start => rfl
  -- Scene 0 only leads to Scene 0.
  | next _ hl ih =>
    subst ih
    obtain ⟨sc, hsc, hid, ch, hch, ht⟩ := hl
    simp only [cheatHiddenEnding, List.mem_cons, List.not_mem_nil, or_false] at hsc
    rcases hsc with rfl | rfl
    · simp only [List.mem_singleton] at hch
      subst hch
      simpa [Outcome.targets] using ht
    · simp at hch

example : ¬ LegalAdventure mara cheatHiddenEnding := by
  intro h
  have h1 := hiddenEnding_only_start
    (h.2.2.2.2 { id := 1, title := "Hidden End", text := "", choices := [] } (by simp [cheatHiddenEnding]))
  simp at h1
example : check mara cheatHiddenEnding ≠ [] := by decide

/-- Cheat 7: a roll the Character can never make. Mara's Diplomacy is 11, so at -10 the
effective skill is 1. The Engine never rolls below 3, so it always takes the failure branch
back to the start, and the Player loops forever. -/
def cheatUnrollable : Adventure :=
  oneChoice "Roll that can't be made" (.roll (.skill .diplomacy) (-10) 1 0)

example : ¬ LegalAdventure mara cheatUnrollable := fun h => absurd h.2.2.2.1 (by decide)
example : check mara cheatUnrollable ≠ [] := by decide

/-- All the cheating Adventures, for the demo. -/
def cheats : List Adventure :=
  [cheatGiant, cheatBrokenLink, cheatEasyLock, cheatEndless, cheatNoEnding, cheatHiddenEnding,
    cheatUnrollable]

end Rpg
