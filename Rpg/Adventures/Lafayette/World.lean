import Rpg.Adventures.Lafayette.Story
import Rpg.Environment

/-!
# What the Player sees around Lafayette at Barren Hill

The World, the Intro, the Character's background, and the world map for the 3D page. These change
only what the Player sees. No rule and no proof looks at them.
-/

namespace Rpg.Lafayette

/-- The World of the built-in Adventure. -/
def world : String := "Pennsylvania, May 1778, the American War of Independence"

/-- The Intro: the text that the Player reads before the first Scene. -/
def intro : String :=
  "Pennsylvania, in the spring of 1778. The Continental Army has lived through the winter at Valley Forge, and the British army holds Philadelphia. You are the Marquis de Lafayette, a young French noble who crossed the sea to fight for American freedom. You are good with a sword, with a horse, and with words."

/-- The Character's background, for the card on the Front Page. -/
def background : String :=
  "A French noble who came to America in 1777, at nineteen, and became a major general under Washington. He was wounded at Brandywine and wintered with the army at Valley Forge."

/-- The world map for the 3D page: a forest theme, with one place for each part of the story. -/
def worldMap : WorldEnvironment where
  theme := "forest"
  places := [
    { id := 0, name := "Valley Forge", kind := "camp", x := -70, z := 60 },
    { id := 1, name := "Militia Camp", kind := "camp", x := -25, z := 70 },
    { id := 2, name := "Barren Hill Church", kind := "temple", x := 10, z := 30 },
    { id := 3, name := "The Ridge", kind := "outpost", x := 55, z := 50 },
    { id := 4, name := "Road to the Ford", kind := "forest", x := 0, z := -10 },
    { id := 5, name := "Cattle Path", kind := "forest", x := 45, z := -40 },
    { id := 6, name := "Matson's Ford", kind := "village", x := -35, z := -45 },
    { id := 7, name := "West Bank", kind := "camp", x := -5, z := -75 } ]
  paths := [
    { fromPlace := 0, toPlace := 1 }, { fromPlace := 0, toPlace := 2 },
    { fromPlace := 1, toPlace := 2 }, { fromPlace := 2, toPlace := 3 },
    { fromPlace := 2, toPlace := 4 }, { fromPlace := 3, toPlace := 4 },
    { fromPlace := 4, toPlace := 5 }, { fromPlace := 4, toPlace := 6 },
    { fromPlace := 5, toPlace := 7 }, { fromPlace := 6, toPlace := 7 } ]
  props := [
    { kind := "tent", x := -78, z := 80 }, { kind := "tent", x := -52, z := 78 },
    { kind := "house", x := -50, z := 40, scale := 80 },
    { kind := "tree", x := -10, z := 85 }, { kind := "tree", x := 30, z := 75 },
    { kind := "tree", x := 75, z := 20 }, { kind := "tree", x := 30, z := 5 },
    { kind := "tree", x := -30, z := 15 }, { kind := "tree", x := 70, z := -15 },
    { kind := "tree", x := 75, z := -60 }, { kind := "rock", x := 25, z := -70 },
    { kind := "house", x := -65, z := -25, scale := 80 },
    { kind := "river", x := -40, z := -70, scale := 200, heading := 30 },
    { kind := "river", x := 20, z := -55, scale := 200, heading := 30 } ]
  scenes := [
    { scene := 0, place := 0, npcs := ["General Washington"] },
    { scene := 1, place := 1, npcs := ["Captain Hollis"] },
    { scene := 2, place := 2, npcs := ["Militia Boy"] },
    { scene := 3, place := 2 },
    { scene := 4, place := 2, npcs := ["Captain Hollis"] },
    { scene := 5, place := 3 },
    { scene := 6, place := 2 },
    { scene := 7, place := 4, npcs := ["Jem"] },
    { scene := 8, place := 5, npcs := ["Jem"] },
    { scene := 9, place := 6 },
    { scene := 10, place := 7, npcs := ["Oneida Warrior"] },
    { scene := 11, place := 7 },
    { scene := 12, place := 7, npcs := ["Oneida Warrior"] },
    { scene := 13, place := 7 } ]

-- The 3D page can draw the map, and each Scene has one place.
#guard worldMap.errors barrenHill == []

end Rpg.Lafayette
