import Rpg.Adventures.Lighthouse.Story
import Rpg.Probability.Fairness

namespace Rpg.Lighthouse

/-- Lighthouse and its derived HP-aware graph; finite fairness is supplied by `Confidence.lean`. -/
def lighthouseDefinition : Probability.AdventureDefinition :=
  ⟨rules, mara, mara_legal, lighthouse, lighthouse_legal⟩

end Rpg.Lighthouse
