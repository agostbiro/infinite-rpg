import Rpg.Adventures.Lafayette.Story
import Rpg.Probability.Balance

namespace Rpg.Lafayette

/-- The built-in Adventure with its rules, Lafayette, and the proofs that both are legal.
The balance check for it is in `Confidence.lean`. -/
def barrenHillDefinition : AdventureDefinition :=
  ⟨rules, lafayette, lafayette_legal, barrenHill, barren_hill_legal⟩

end Rpg.Lafayette
