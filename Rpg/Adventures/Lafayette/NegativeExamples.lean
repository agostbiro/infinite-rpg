import Rpg.Adventures.Lafayette

/-!
# Broken copies of Lafayette at Barren Hill

Each Adventure here is the built-in Adventure with one Scene changed, the way a cheating DM could
change it. For each one we show two things: the spec rejects it, and the checker reports an error.
The last copy breaks the short-loop rule, so for it we show that `NoShortLoops` fails.
-/

namespace Rpg.Lafayette.Tests

/-- The built-in Adventure, with the Scene that has the number of `sc` replaced by `sc`. -/
def withScene (sc : Scene) : Adventure :=
  { barrenHill with scenes := barrenHill.scenes.map fun s => if s.id == sc.id then sc else s }

/-- Cheat 1: the jägers at the ford have ST 40. -/
def cheatGiantJagers : Adventure := withScene
  { id := 9, title := "Ambush at Matson's Ford", text := "",
    choices := [{ text := "Fight the jägers", outcome := .fight [{ jager 1 with st := 40 }] 10 }] }

example : ¬ LegalAdventure rules lafayette cheatGiantJagers := fun h => absurd h.2.2.2.1 (by decide)
example : check rules lafayette cheatGiantJagers ≠ [] := by decide

/-- Cheat 2: the road to the ford leads to a Scene that does not exist. -/
def cheatLostRoad : Adventure := withScene
  { id := 7, title := "The Road to Matson's Ford", text := "",
    choices := [{ text := "March the men straight down to the ford", outcome := .goto 99 }] }

example : ¬ LegalAdventure rules lafayette cheatLostRoad := fun h => absurd h.2.2.2.1 (by decide)
example : check rules lafayette cheatLostRoad ≠ [] := by decide

/-- Cheat 3: the militia captain is won over at Diplomacy +15, far beyond the limit of +10. -/
def cheatEasyCaptain : Adventure := withScene
  { id := 1, title := "The Militia Camp", text := "",
    choices := [{ text := "Ask him", outcome := .roll (.skill .diplomacy) 15 2 3 }] }

example : ¬ LegalAdventure rules lafayette cheatEasyCaptain := fun h => absurd h.2.2.2.1 (by decide)
example : check rules lafayette cheatEasyCaptain ≠ [] := by decide

/-- Cheat 4: a roll that Lafayette can never make. His Stealth is 11, so at -10 the effective
skill is 1, below the minimum of 3. -/
def cheatHopelessStealth : Adventure := withScene
  { id := 8, title := "The Cattle Path", text := "",
    choices := [{ text := "Creep up behind him", outcome := .roll (.skill .stealth) (-10) 10 9 }] }

example : ¬ LegalAdventure rules lafayette cheatHopelessStealth := fun h => absurd h.2.2.2.1 (by decide)
example : check rules lafayette cheatHopelessStealth ≠ [] := by decide

/-- Cheat 5: the ambush at the ford leads back to the road, so the road and the ford make a loop
of 2 steps. -/
def cheatShortLoop : Adventure := withScene
  { id := 9, title := "Ambush at Matson's Ford", text := "",
    choices := [{ text := "Fight the jägers", outcome := .fight [jager 1, jager 2] 10 },
                { text := "Run back up the road", outcome := .goto 7 }] }

example : ¬ cheatShortLoop.NoShortLoops := by decide
example : cheatShortLoop.checkShortLoops = false := by decide

/-- A Character that the spec rejects: Lafayette with DX 15, above the limit of 14. -/
example : ¬ LegalCharacter rules { lafayette with dx := 15 } := by decide

end Rpg.Lafayette.Tests
