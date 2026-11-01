import Rpg.Adventures.Harbor.Characters

namespace Rpg.Harbor

/-- A one-turn tutorial used to demonstrate an adventure with a fairness certificate. -/
def harbor : Adventure where
  title := "A Safe Harbor"
  start := 0
  scenes := [
    { id := 0, title := "The Harbor", text := "You reach the harbor before the storm. The keeper waves you toward shelter."
      choices := [{ text := "Take shelter", outcome := .goto 1 }] },
    { id := 1, title := "Safe Ashore", text := "You wait out the storm beside the fire. Your journey ends safely."
      choices := [] } ]

/-- The tutorial obeys all existing adventure rules. -/
theorem harbor_legal : LegalAdventure rules iona harbor := check_sound (by decide)

end Rpg.Harbor
