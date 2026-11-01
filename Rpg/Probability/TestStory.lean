import Rpg.Adventures.TestAdventure.Characters
import Rpg.Probability.StatisticalAdmission

/-!
# A safe test story

A two-Scene story with no danger, for tests only. It is not in the catalog, so it is never
offered for play. The tests use it to show that the hypotheses of `balanced` can all be met on a
real candidate. It also shows where admission rejects a story where the Character can never die.
-/

namespace Rpg.Probability.TestStory

/-- One Choice, then an Ending. -/
def safeStory : Adventure where
  title := "Safe Shelter"
  start := 0
  scenes := [
    { id := 0, title := "The Storm", text := "A storm comes. A farmer waves you inside."
      choices := [{ text := "Take shelter", outcome := .goto 1 }] },
    { id := 1, title := "Safe Inside", text := "You wait out the storm by the fire."
      choices := [] } ]

/-- The safe story is legal for Mara under the default rules. -/
theorem safeStory_legal : LegalAdventure {} TestAdventure.mara safeStory := check_sound (by decide)

/-- The safe story with Mara, under the default rules. -/
def safeDefinition : AdventureDefinition :=
  ⟨{}, TestAdventure.mara, TestAdventure.mara_legal, safeStory, safeStory_legal⟩

/-- The safe story as a candidate with horizon 1. -/
def safeCandidate : StatisticalCandidate where
  toAdventureDefinition := safeDefinition
  horizon := 1
  horizonPositive := by decide

/-- The safe story with horizon 5, as for a Wish. -/
def safeCandidate5 : StatisticalCandidate where
  toAdventureDefinition := safeDefinition
  horizon := 5
  horizonPositive := by decide

-- With horizon 1 the safe story passes the medium curve (the default): the bands of rows 0 and 1
-- start at 0. On medium the check can reject an Adventure with no deaths only from row 2 on, so a
-- candidate needs horizon 2 or more for that.
#guard (admitWithSeed safeCandidate 1).2.isSome
-- With horizon 5, as for the test Adventure and every Wish, admission rejects the safe story.
#guard (admitWithSeed safeCandidate5 1).2.isNone

end Rpg.Probability.TestStory
