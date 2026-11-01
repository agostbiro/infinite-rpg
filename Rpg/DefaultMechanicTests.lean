import Rpg.WorldChangeTests

/-! The shared defaults affect actual attacks and are inherited by generated adventures. -/
namespace Rpg.DefaultMechanicTests

/-- Critical fixed dice make hit levels and damage effects deterministic. -/
private def ones (n : Nat) : Id (List Nat) := pure (List.replicate n 1)

/-- The attack target recorded by the actual engine. -/
private def target (reports : List Report) : Option Int :=
  reports.findSome? fun r => match r with
    | .attack _ _ _ _ _ _ roll => some roll.target
    | _ => none

/-- Both authored adventures and new Wishes inherit the same meta rules. -/
theorem shared_defaults :
    Lighthouse.rules.combatRules = defaultCombatRules ∧
    liveRules.combatRules = defaultCombatRules := ⟨rfl, rfl⟩

-- All-Out Attack gets real additional injury and an explanation in the combat log.
#guard
  let hero : Fighter := { being := Lighthouse.mara, hp := 11, maneuver := .allOutAttack }
  let foe : Fighter := { being := Lighthouse.wrecker 1, hp := 10 }
  let plain := (attackWith { combatRules := [] } ones none hero (some 0) foe).run
  let changed := (attackWith {} ones none hero (some 0) foe).run
  changed.1 > plain.1 && changed.2.contains (.worldRule committedStrike.name committedStrike.description)

-- Guard Feint reduces an enemy's actual attack target and does not alter normal attacks.
#guard
  let hero : Fighter := { being := Lighthouse.mara, hp := 11, maneuver := .allOutDefense }
  let foe : Fighter := { being := Lighthouse.wrecker 1, hp := 10 }
  target (attackWith {} ones (some 0) foe none hero).run.2 == some 10 &&
    target (attackWith {} ones (some 0) foe none { hero with maneuver := .attack }).run.2 == some 11

-- Wounded enemies rally, but an equally wounded hero never receives the enemy-only bonus.
#guard
  let hero : Fighter := { being := Lighthouse.mara, hp := 11 }
  let foe : Fighter := { being := Lighthouse.wrecker 1, hp := 5 }
  target (attackWith {} ones (some 0) foe none hero).run.2 == some 13 &&
    !corneredFury.active {} none { hero with hp := 1 } foe

-- Reckless attacks expose the hero to extra enemy injury; guarding avoids that counter-rule.
#guard
  let hero : Fighter := { being := Lighthouse.mara, hp := 11, maneuver := .allOutAttack }
  let foe : Fighter := { being := Lighthouse.wrecker 1, hp := 10 }
  (attackWith {} ones (some 0) foe none hero).run.1 >
    (attackWith { combatRules := [] } ones (some 0) foe none hero).run.1 &&
    !punishOpening.active {} (some 0) foe { hero with maneuver := .allOutDefense }

-- The action preview includes the real tradeoff before a player commits.
#guard match fightGame.phase with
  | .fight f =>
    (maneuverEffects {} f .allOutAttack).length ≥ 2 &&
    (maneuverEffects {} f .allOutDefense).any (·.startsWith "Guard Feint:")
  | _ => false

end Rpg.DefaultMechanicTests
