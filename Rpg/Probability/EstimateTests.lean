import Rpg.Probability.Estimate
import Rpg.Probability.RuleSetExamples
import Rpg.Adventures.Harbor

/-! Regression tests for diagnostics. These establish implementation examples,
not concentration inequalities or a statistical fairness certificate. -/
namespace Rpg.Probability.Estimate

/-- A cheap, reproducible diagnostic fixture. -/
def testConfig : Config := { samples := 20, horizon := 4, roundLimit := 2, seed := 7 }

-- A safe ending occurs on its actual scene-choice turn.
#guard ((trajectory Harbor.harborCertified.toAdventureDefinition 2 6
  Harbor.harbor.start (Harbor.rules.maxHP Harbor.iona) 0).run ⟨7⟩).1 == ⟨.ended, 1⟩
-- Fuel exhaustion is recorded as unknown, not as an ending or death.
#guard ((trajectory Harbor.harborCertified.toAdventureDefinition 2 0
  Harbor.harbor.start (Harbor.rules.maxHP Harbor.iona) 0).run ⟨7⟩).1 == ⟨.censored, 1⟩
-- A completed fight is recognized even when no further round budget remains.
#guard ((fight fixtureRules [] 0 ⟨⟨strongHero, 3⟩, []⟩).run ⟨7⟩).1.isSome
-- A genuine unresolved fight is not classified as a loss.
#guard ((fight failureRules (turnOrder failureRules strongHero [harmlessFoe]) 2
  ⟨⟨strongHero, 3⟩, [⟨harmlessFoe, 1⟩]⟩).run ⟨7⟩).1.isNone

/-- Fixture counts must retain every run. -/
def safeCounts : Counts := sample testConfig Harbor.harborCertified.toAdventureDefinition
#guard total safeCounts.endings == 20
#guard total safeCounts.deaths == 0
#guard total safeCounts.censored == 0
#guard safeCounts.endings[1]! == 20
#guard (conditionalDeathTime testConfig safeCounts).isNone
-- Zero observed deaths does not turn into a zero-width confidence interval.
#guard (firstDeath testConfig safeCounts).upper > 0
-- No observed active games does not become a passing conditional test.
#guard (atTwo testConfig safeCounts 3).lower == 0
#guard (atTwo testConfig safeCounts 3).upper == 1

#guard classify ⟨0.1, 0.2⟩ ⟨0.12, 0.18⟩ == .within
#guard classify ⟨0.1, 0.2⟩ ⟨0.15, 0.25⟩ == .inconclusive
#guard classify ⟨0.1, 0.2⟩ ⟨0.3, 0.4⟩ == .violation
#guard classify ⟨0.1, 0.2⟩ ⟨0, 1⟩ == .inconclusive

/-- All-censored data must not produce a spurious confident result. -/
def censoredCounts : Counts := ⟨#[0, 0, 0, 0], #[0, 0, 0, 0], #[0, 20, 0, 0], 0⟩
#guard (firstDeath testConfig censoredCounts).upper == 1
#guard (atTwo testConfig censoredCounts 0).upper == 1
#guard (terminationTime testConfig censoredCounts).upper == (testConfig.horizon + 2).toFloat

end Rpg.Probability.Estimate
