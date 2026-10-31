import Rpg.Check

/-!
# Ready-made Characters

Each Character is a legal 100-point build, proved by the checker.
-/

namespace Rpg

/-- Mara, a sellsword. 100 points: attributes 70, skills 30. -/
def mara : Being where
  name := "Mara"
  st := 11
  dx := 12
  iq := 10
  ht := 12
  skills := [(.broadsword, 14), (.stealth, 13), (.lockpicking, 12), (.diplomacy, 11),
             (.brawling, 12), (.knife, 12)]
  weapon := .broadsword
  armor := .leather

#guard mara.points == 100

/-- Mara is a legal Character. -/
theorem mara_legal : LegalCharacter mara :=
  checkCharacter_sound (by decide)

end Rpg
