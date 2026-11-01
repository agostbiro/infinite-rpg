import Rpg.Adventures.Lighthouse.Characters

/-!
# The Drowned Lighthouse

A short Adventure written by the DM. The theorem `lighthouse_legal` at the end
proves that it is legal for Mara. If the DM breaks a rule, the build fails.
-/

namespace Rpg.Lighthouse

/-- The Drowned Lighthouse. -/
def lighthouse : Adventure where
  title := "The Drowned Lighthouse"
  start := 0
  scenes := [
    { id := 0, title := "The Shore"
      text := "Rain lashes the shingle. The lighthouse on the rock went dark three nights ago, and two ships have broken on the reef since. The keeper's daughter grips your arm: \"My father is still out there.\" A causeway runs to the rock, half under the tide. A goat path climbs the cliff behind the tower."
      choices := [
        { text := "Wade the causeway to the front door", outcome := .goto 1 },
        { text := "Climb the goat path (DX -2)", outcome := .roll (.attribute .dx) (-2) 2 1 } ] },
    { id := 1, title := "The Iron Door"
      text := "The tower door is iron, swollen with salt, and locked. Through the keyhole you hear men laughing and dice rattling."
      choices := [
        { text := "Pick the lock quietly (Lockpicking)", outcome := .roll (.skill .lockpicking) 0 3 4 },
        { text := "Hammer on the door", outcome := .goto 4 } ] },
    { id := 2, title := "The Gallery"
      text := "You haul yourself onto the iron gallery that rings the top of the tower. A cracked window opens onto the lamp room."
      choices := [
        { text := "Slip through the window", outcome := .goto 5 } ] },
    { id := 3, title := "The Store Room"
      text := "The lock gives with a soft click. Inside, two wreckers play dice by a lantern, their backs to the stair."
      choices := [
        { text := "Creep past them up the stair (Stealth -2)", outcome := .roll (.skill .stealth) (-2) 5 4 },
        { text := "Attack while they are distracted", outcome := .goto 4 } ] },
    { id := 4, title := "Wreckers!"
      text := "Two wreckers come at you with long knives, cursing."
      choices := [
        { text := "Fight", outcome := .fight [wrecker 1, wrecker 2] 5 } ] },
    { id := 5, title := "The Lamp Room"
      text := "The great lamp is cold. The keeper sits bound to a chair. Over him stands Grey Hollis, sword drawn. \"Ships on the reef mean cargo on the beach,\" he says. \"Walk away.\""
      choices := [
        { text := "Talk him down (Diplomacy -3)", outcome := .roll (.skill .diplomacy) (-3) 7 6 },
        { text := "Draw your sword", outcome := .goto 6 } ] },
    { id := 6, title := "Steel in the Dark"
      text := "Hollis laughs and comes at you."
      choices := [
        { text := "Fight Grey Hollis", outcome := .fight [hollis] 8 } ] },
    { id := 7, title := "Ending: The Light Returns"
      text := "Hollis weighs your words, and your sword, and lowers his blade. He walks out into the rain. You free the keeper, and together you light the lamp. Far out at sea, a ship turns away from the reef."
      choices := [] },
    { id := 8, title := "Ending: The Keeper's Debt"
      text := "Hollis falls. You cut the keeper free, and his trembling hands relight the lamp. \"The light will burn every night while I live,\" he says. \"And you will never pay for a meal in this village again.\""
      choices := [] } ]

/-- **The Drowned Lighthouse is legal for Mara.** The Lean kernel runs the checker to prove it. -/
theorem lighthouse_legal : LegalAdventure rules mara lighthouse :=
  check_sound (by decide)

end Rpg.Lighthouse
