import Rpg.Probability.Simulation
import Rpg.Probability.RuleSetExamples
import Rpg.Adventures.Harbor

namespace Rpg.Probability.Simulation

-- A safe ending occurs on its actual scene-choice turn.
#guard ((trajectory Harbor.harborDefinition 2 6
  Harbor.harbor.start (Harbor.rules.maxHP Harbor.iona) 0).run ⟨7⟩).1 == ⟨.ended, 1⟩
-- Fuel exhaustion is recorded as unknown, not as an ending or death.
#guard ((trajectory Harbor.harborDefinition 2 0
  Harbor.harbor.start (Harbor.rules.maxHP Harbor.iona) 0).run ⟨7⟩).1 == ⟨.censored, 1⟩
-- A completed fight is recognized even when no further round budget remains.
#guard ((fight fixtureRules [] 0 ⟨⟨strongHero, 3⟩, []⟩).run ⟨7⟩).1.isSome
-- A genuine unresolved fight is not classified as a loss.
#guard ((fight failureRules (turnOrder failureRules strongHero [harmlessFoe]) 2
  ⟨⟨strongHero, 3⟩, [⟨harmlessFoe, 1⟩]⟩).run ⟨7⟩).1.isNone

end Rpg.Probability.Simulation
