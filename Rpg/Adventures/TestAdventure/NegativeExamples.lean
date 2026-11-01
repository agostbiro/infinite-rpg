import Rpg.Adventures.TestAdventure

/-!
# Illegal Adventures

Each Adventure here breaks one rule, the way a cheating DM might.
For each one we show two things:
the spec rejects it (`¬ LegalAdventure`), and the checker reports an error.
Each spec proof picks out the rule that the cheat breaks and shows by `decide` that the rule fails.
-/

namespace Rpg.TestAdventure.Tests

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

example : ¬ LegalAdventure rules mara cheatGiant := fun h => absurd h.2.2.2.1 (by decide)
example : check rules mara cheatGiant ≠ [] := by decide

/-- Cheat 2: a Choice that leads to a Scene that does not exist. -/
def cheatBrokenLink : Adventure := oneChoice "Broken link" (.goto 99)

example : ¬ LegalAdventure rules mara cheatBrokenLink := fun h => absurd h.2.2.2.1 (by decide)
example : check rules mara cheatBrokenLink ≠ [] := by decide

/-- Cheat 3: a lock at +15, far beyond the limit of +10. -/
def cheatEasyLock : Adventure := oneChoice "Easy lock" (.roll (.skill .lockpicking) 15 1 1)

example : ¬ LegalAdventure rules mara cheatEasyLock := fun h => absurd h.2.2.2.1 (by decide)
example : check rules mara cheatEasyLock ≠ [] := by decide

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

example : ¬ LegalAdventure rules mara cheatEndless := fun h => absurd h.2.2.2.1 (by decide)
example : check rules mara cheatEndless ≠ [] := by decide

/-- Cheat 5: no Ending, so the Adventure goes on forever. -/
def cheatNoEnding : Adventure where
  title := "No ending"
  start := 0
  scenes := [{ id := 0, title := "Loop", text := "", choices := [{ text := "Again", outcome := .goto 0 }] }]

example : ¬ LegalAdventure rules mara cheatNoEnding := fun h => absurd h.2.2.1 (by decide)
example : check rules mara cheatNoEnding ≠ [] := by decide

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

example : ¬ LegalAdventure rules mara cheatHiddenEnding := by
  intro h
  have h1 := hiddenEnding_only_start
    (h.2.2.2.2.1 { id := 1, title := "Hidden End", text := "", choices := [] } (by simp [cheatHiddenEnding]))
  simp at h1
example : check rules mara cheatHiddenEnding ≠ [] := by decide

/-- Cheat 7: a roll the Character can never make. Mara's Diplomacy is 11, so at -10 the
effective skill is 1. The Engine never rolls below 3, so it always takes the failure branch
back to the start, and the Player loops forever. -/
def cheatUnrollable : Adventure :=
  oneChoice "Roll that can't be made" (.roll (.skill .diplomacy) (-10) 1 0)

example : ¬ LegalAdventure rules mara cheatUnrollable := fun h => absurd h.2.2.2.1 (by decide)
example : check rules mara cheatUnrollable ≠ [] := by decide

/-- Cheat 8: a trap with no way out. Every Scene can be reached and an Ending exists,
but the maze only leads back into the maze. A Player who goes in can never reach an Ending. -/
def cheatTrap : Adventure where
  title := "Trap with no way out"
  start := 0
  scenes := [
    { id := 0, title := "Fork", text := "", choices := [
        { text := "Go home", outcome := .goto 1 },
        { text := "Enter the maze", outcome := .goto 2 }] },
    { id := 1, title := "Home", text := "", choices := [] },
    { id := 2, title := "Maze", text := "", choices := [{ text := "Walk on", outcome := .goto 2 }] } ]

/-- In the trap Adventure, an Ending can never be reached from the maze (Scene 2). -/
theorem trap_no_way_out {x : SceneId}
    (h : ReachesEnding cheatTrap x) : x ≠ 2 := by
  induction h with
  -- The only Ending is Scene 1, which is not the maze.
  | ending he =>
    obtain ⟨sc, hsc, rfl, hnil⟩ := he
    simp only [cheatTrap, List.mem_cons, List.not_mem_nil, or_false] at hsc
    rcases hsc with rfl | rfl | rfl
    -- The fork has Choices, so it is not an Ending.
    · simp at hnil
    -- Home is Scene 1, not the maze.
    · decide
    -- The maze has a Choice, so it is not an Ending.
    · simp at hnil
  -- A Choice in the maze leads only back into the maze.
  | next hl _ ih =>
    rintro rfl
    obtain ⟨sc, hsc, hid, ch, hch, ht⟩ := hl
    simp only [cheatTrap, List.mem_cons, List.not_mem_nil, or_false] at hsc
    rcases hsc with rfl | rfl | rfl
    -- The fork is Scene 0, not the maze.
    · simp at hid
    -- Home is Scene 1, not the maze.
    · simp at hid
    -- The maze's one Choice leads to the maze.
    · simp only [List.mem_singleton] at hch
      subst hch
      simp only [Outcome.targets, List.mem_singleton] at ht
      exact ih ht

example : ¬ LegalAdventure rules mara cheatTrap := by
  intro h
  have h2 := trap_no_way_out
    (h.2.2.2.2.2 { id := 2, title := "Maze", text := "", choices := [{ text := "Walk on", outcome := .goto 2 }] }
      (by simp [cheatTrap]))
  exact h2 rfl
example : check rules mara cheatTrap ≠ [] := by decide

/-- All the cheating Adventures, for the demo. -/
def cheats : List Adventure :=
  [cheatGiant, cheatBrokenLink, cheatEasyLock, cheatEndless, cheatNoEnding, cheatHiddenEnding,
    cheatUnrollable, cheatTrap]

end Rpg.TestAdventure.Tests
