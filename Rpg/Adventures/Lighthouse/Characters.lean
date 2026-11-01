import Rpg.Check
import Rpg.Adventures.Lighthouse.Rules

/-!
# Ready-made Characters

Each Character is a legal 100-point build, proved by the checker.
-/

namespace Rpg.Lighthouse

/-- Mara, a sellsword. 100 points: attributes 70, skills 30. -/
def mara : Being where
  name := "Mara"
  st := 11 /- Strength -/
  dx := 12 /- Dexterity -/
  iq := 10 /- IQ -/
  ht := 12 /- Health -/
  skills := [(.broadsword, 14), (.stealth, 13), (.lockpicking, 12), (.diplomacy, 11),
             (.brawling, 12), (.knife, 12)]
  weapon := .broadsword
  armor := .leather

#guard mara.points == 100
-- Mara attacks with her broadsword at Broadsword-14.
#guard mara.attackLevel == 14

/-- Mara is a legal Character. -/
theorem mara_legal : LegalCharacter rules mara :=
  checkCharacter_sound (by decide)

/-- A wrecker: a coastal thug with a knife. -/
def wrecker (n : Nat) : Being where
  name := s!"Wrecker {n}"
  st := 10
  dx := 10
  iq := 9
  ht := 10
  skills := [(.knife, 11)]
  weapon := .largeKnife
  armor := .none

/-- Grey Hollis, leader of the wreckers. -/
def hollis : Being where
  name := "Grey Hollis"
  st := 12
  dx := 11
  iq := 11
  ht := 11
  skills := [(.broadsword, 13), (.diplomacy, 9)]
  weapon := .broadsword
  armor := .leather

/-- The keeper can knock away Hollis's sword, leaving his less-practiced knife. -/
def disarmedHollis : Being :=
  { hollis with
    name := "Hollis, Sword Lost", weapon := .largeKnife,
    skills := [(.knife, 11), (.diplomacy, 9)] }

end Rpg.Lighthouse
