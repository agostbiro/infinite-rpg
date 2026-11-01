import Rpg.Adventures.Lighthouse.Story
import Rpg.Probability.Fairness

namespace Rpg.Lighthouse

/-- Lighthouse and its derived HP-aware graph; fairness is not yet certified. -/
def lighthouseDefinition : Probability.AdventureDefinition :=
  ⟨rules, mara, mara_legal, lighthouse, lighthouse_legal⟩

end Rpg.Lighthouse
