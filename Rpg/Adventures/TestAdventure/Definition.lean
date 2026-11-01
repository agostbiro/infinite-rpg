import Rpg.Adventures.TestAdventure.Story
import Rpg.Probability.Balance

namespace Rpg.TestAdventure

/-- The test Adventure with its rules, Mara, and the proofs that both are legal.
The balance check for it is in `Confidence.lean`. -/
def testAdventureDefinition : AdventureDefinition :=
  ⟨rules, mara, mara_legal, testAdventure, test_adventure_legal⟩

end Rpg.TestAdventure
