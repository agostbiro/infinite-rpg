import Rpg.Check
import Rpg.Adventures.Lafayette.Rules

/-!
# The Character and the foes of Lafayette at Barren Hill

The Character is the Marquis de Lafayette, a young French noble and a major general of the
Continental Army. He is a legal 100-point build, proved by the checker. The foes fight for the
British in 1778: grenadiers, Hessian jägers, a Loyalist scout, and dragoons. Their names are
invented.
-/

namespace Rpg.Lafayette

/-- Lafayette, a noble officer. 100 points: attributes 70, skills 30. -/
def lafayette : Being where
  name := "Lafayette"
  st := 11 /- Strength -/
  dx := 12 /- Dexterity -/
  iq := 11 /- IQ -/
  ht := 10 /- Health -/
  skills := [(.broadsword, 14), (.diplomacy, 12), (.riding, 14), (.survival, 11),
             (.stealth, 11), (.fastTalk, 11), (.firstAid, 11)]
  weapon := .broadsword
  armor := .leather

#guard lafayette.points == 100
-- Lafayette attacks with his sword at Broadsword-14.
#guard lafayette.attackLevel == 14

/-- Lafayette is a legal Character. -/
theorem lafayette_legal : LegalCharacter rules lafayette :=
  checkCharacter_sound (by decide)

/-- A British grenadier with a bayonet. -/
def grenadier (n : Nat) : Being where
  name := s!"Grenadier {n}"
  st := 11
  dx := 10
  iq := 9
  ht := 10
  skills := [(.knife, 10)]
  weapon := .largeKnife
  armor := .none

/-- A Hessian jäger, a rifleman from Hesse, with a hunting sword. -/
def jager (n : Nat) : Being where
  name := s!"Jäger {n}"
  st := 10
  dx := 10
  iq := 10
  ht := 10
  skills := [(.broadsword, 10), (.stealth, 11)]
  weapon := .broadsword
  armor := .none

/-- A Loyalist scout who guides the jägers. He swings his musket like a club. -/
def loyalistScout : Being where
  name := "Loyalist Scout"
  st := 11
  dx := 10
  iq := 10
  ht := 10
  skills := [(.staff, 10), (.survival, 12)]
  weapon := .quarterstaff
  armor := .none

/-- A British dragoon scout on a fast horse. He has no heavy coat. -/
def dragoonScout : Being where
  name := "Dragoon Scout"
  st := 11
  dx := 11
  iq := 10
  ht := 10
  skills := [(.broadsword, 11), (.riding, 13)]
  weapon := .broadsword
  armor := .none

/-- A British dragoon sergeant with a sabre and a heavy riding coat. -/
def dragoon : Being where
  name := "Dragoon Sergeant"
  st := 12
  dx := 11
  iq := 10
  ht := 11
  skills := [(.broadsword, 12), (.riding, 12)]
  weapon := .broadsword
  armor := .leather

end Rpg.Lafayette
