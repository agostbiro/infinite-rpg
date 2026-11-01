import Rpg.Probability.Examples

/-! Regression proofs: changing an adventure's rules must affect both execution
and analysis. A certificate must also validate the adventure's own hero. -/
namespace Rpg.Probability

/-- Test rules in which every success roll fails. -/
def failureRules : RuleSet := { fixtureRules with successRoll := fun _ _ => .failure }

/-- Test rules for a zero-point character, with a different HP scale. -/
def zeroPointRules : RuleSet := { fixtureRules with characterPoints := 0, maxHP := fun _ => 3 }

/-- The same character is legal only under the rules that accept its point budget. -/
example : LegalCharacter zeroPointRules rollHero := by decide +kernel
example : ¬ LegalCharacter fixtureRules rollHero := by decide +kernel

/-- Build diagnostics use the selected point budget. -/
example : checkCharacter zeroPointRules rollHero = [] := by decide +kernel
example : checkCharacter fixtureRules rollHero ≠ [] := by decide +kernel

/-- No attack is falsely declared usable when the local success rule always fails. -/
example : ¬ failureRules.canHurt strongHero harmlessFoe := by decide +kernel

/-- A rule variant with zero injury cannot pass the attack-possibility test. -/
def noInjuryRules : RuleSet := { fixtureRules with injury := fun _ _ _ => 0 }

example : ¬ noInjuryRules.canHurt strongHero harmlessFoe := by decide +kernel

/-- A small graph keeps success and failure distinguishable after a roll. -/
def rulesStory : Adventure where
  title := "Rules fixture"
  start := 0
  scenes := [
    { id := 0, title := "Roll", text := "", choices := [
      { text := "Try", outcome := .roll (.attribute .dx) 0 1 2 }] },
    { id := 1, title := "Success", text := "", choices := [{ text := "End", outcome := .goto 3 }] },
    { id := 2, title := "Failure", text := "", choices := [{ text := "End", outcome := .goto 3 }] },
    { id := 3, title := "End", text := "", choices := [] } ]

/-- The graph's initial HP comes from the adventure's HP rule. -/
example : (adventureGraph zeroPointRules rollHero rulesStory).start = .scene 0 3 := by decide +kernel

/-- Identical scenes acquire different edge probabilities under different rules. -/
example : ((adventureGraph fixtureRules rollHero rulesStory).after 1).mass
    (· == .scene 1 10) = 1 / 2 := by decide +kernel
example : ((adventureGraph failureRules rollHero rulesStory).after 1).mass
    (· == .scene 1 10) = 0 := by decide +kernel

/-- Runtime rolls consume the selected success rule too, for every seed. -/
theorem runtime_failure_rule (seed : Rng) :
    ((makeRoll failureRules "Test" (some 10)).run seed).1.1 = .failure := by
  rfl

-- Exact combat evaluation uses the same variant, rather than the global defaults.
#guard (combatDistribution failureRules strongHero 3 [harmlessFoe]).mass (· == .stalled) == 1

/-- The finite diagnostic must catch the first-turn loophole, even at horizon zero. -/
example : checkFairnessThrough defaultPolicy instantDeathGraph 0 =
    [.firstTurn 1 (1 - defaultPolicy.survival 1)] := by decide +kernel

/-- A valid positive fixture has no finite diagnostic failures. -/
example : checkFairnessThrough defaultPolicy safeGraph 4 = [] := by decide +kernel

/-- Diagnostics reject malformed policies rather than silently skipping all tests. -/
example : (checkFairnessThrough { defaultPolicy with retention := 1 } safeGraph 0).head? =
    some .invalidPolicy := by decide +kernel

end Rpg.Probability
