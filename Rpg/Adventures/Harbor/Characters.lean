import Rpg.Check
import Rpg.Adventures.Harbor.Rules

/-!
# Ready-made Characters

Each Character is a legal 100-point build, proved by the checker.
-/

namespace Rpg.Harbor

/-- Iona, a traveler. 100 points: attributes 70, skills 30. -/
def iona : Being where
  name := "Iona"
  st := 11
  dx := 12
  iq := 10
  ht := 12
  skills := [(.broadsword, 14), (.stealth, 13), (.lockpicking, 12), (.diplomacy, 11),
             (.brawling, 12), (.knife, 12)]
  weapon := .broadsword
  armor := .leather

#guard iona.points == 100

/-- Iona is a legal Character. -/
theorem iona_legal : LegalCharacter rules iona :=
  checkCharacter_sound (by decide)

end Rpg.Harbor
