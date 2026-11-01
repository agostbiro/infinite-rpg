import Rpg.Check
import Rpg.Adventures.Lighthouse.Rules

/-!
# Ready-made Characters

Each Character is a legal 100-point build, proved by the checker.
-/

namespace Rpg.Lighthouse

/-- Mara, a sellsword with a flamethrower. 100 points: attributes 70, skills 30. -/
def mara : Being where
  name := "Mara"
  st := 11
  dx := 12
  iq := 10
  ht := 12
  skills := [(.liquidProjector, 15), (.stealth, 13), (.lockpicking, 12), (.diplomacy, 11),
             (.brawling, 12), (.knife, 12)]
  weapon := .flamethrower
  armor := .leather

#guard mara.points == 100
-- Mara fires the flamethrower at Liquid Projector 15.
#guard mara.attackLevel == 15

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

end Rpg.Lighthouse
