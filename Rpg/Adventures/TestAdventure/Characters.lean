import Rpg.Check
import Rpg.Adventures.TestAdventure.Rules

/-!
# Ready-made Characters

Each Character is a legal 100-point build, proved by the checker.
-/

namespace Rpg.TestAdventure

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

/-- A bandit with a knife. -/
def bandit (n : Nat) : Being where
  name := s!"Bandit {n}"
  st := 10
  dx := 10
  iq := 9
  ht := 10
  skills := [(.knife, 11)]
  weapon := .largeKnife
  armor := .none

/-- The bandit chief, with a sword. -/
def chief : Being where
  name := "The Bandit Chief"
  st := 12
  dx := 11
  iq := 11
  ht := 11
  skills := [(.broadsword, 13), (.diplomacy, 9)]
  weapon := .broadsword
  armor := .leather

/-- The chief after he loses his sword: he fights with his knife, which he uses less well. -/
def disarmedChief : Being :=
  { chief with
    name := "The Chief, Sword Lost", weapon := .largeKnife,
    skills := [(.knife, 11), (.diplomacy, 9)] }

end Rpg.TestAdventure
