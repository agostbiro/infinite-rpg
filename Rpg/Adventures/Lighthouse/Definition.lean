import Rpg.Adventures.Lighthouse.Story
import Rpg.Probability.Balance

namespace Rpg.Lighthouse

/-- The Lighthouse with its rules, Mara, and the proofs that both are legal.
The balance check for it is in `Confidence.lean`. -/
def lighthouseDefinition : AdventureDefinition :=
  ⟨rules, mara, mara_legal, lighthouse, lighthouse_legal⟩

end Rpg.Lighthouse
