import Rpg.WorldChangePrompt
import Rpg.Probability.ConfidenceTests

/-! Regression checks for real adventure changes, their scope, and paused combat.
Large fairness batches run through the compiled change-check executable. -/
namespace Rpg.WorldChange.Tests
open Probability Probability.Confidence

/-- An equipment gift retains the flamethrower's full 3d spray attack. -/
def flame : EquipmentRule :=
  ⟨"Mara", .flamethrower, "Stormglass Flamethrower", 12, 3, 0⟩

/-- Wounded enemies rally; the player can finish them before they counterattack. -/
def fury : CombatRule :=
  { name := "Scorched Fury", description := "Enemies at half HP or less gain +3 to hit and +2 damage. Finish them before they rally!",
    side := "foes", trigger := "wounded", hitBonus := 3, damageBonus := 2 }

/-- A guarded turn offers a visible way to weather the enemies' retaliation. -/
def shelter : CombatRule :=
  { name := "Cinder Veil", description := "All-Out Defense wraps you in ash: +2 armor until your next maneuver.",
    side := "hero", trigger := "guarding", armorBonus := 2 }

/-- A deterministic proposal fixture; numbers are tuned only with the screening seed. -/
def proposal : Proposal :=
  { summary := "You catch a Stormglass Flamethrower, its enchanted sight guiding your aim.",
    moment := "Wounded wreckers rally through the smoke. Finish them or guard behind a Cinder Veil.",
    equipment := some flame, rules := [fury, shelter], scenes := [] }

-- A missing counter-rule, an impossible trigger, and rewritten history are rejected.
#guard !({ proposal with rules := [] }.errors shoreGame).isEmpty
#guard !({ proposal with rules := [{ fury with trigger := "heal" }] }.errors shoreGame).isEmpty
#guard !({ proposal with rules := [{ fury with trigger := "guarding" }] }.errors shoreGame).isEmpty
#guard !({ proposal with scenes := Lighthouse.lighthouse.scenes.take 1 }.errors shoreGame).isEmpty
#guard !(proposal.errors titleGame).isEmpty
#guard !({ proposal with rules := [{ fury with trigger := "always" }] }.errors shoreGame).isEmpty

/-- A non-weapon request demonstrates that the same path accepts a general combat effect. -/
def ironSkin : Proposal :=
  { proposal with
    equipment := none
    requestedRules := [{
      name := "Iron Skin"
      description := "Your skin gains 2 armor."
      side := "hero", trigger := "always", armorBonus := 2 }] }

-- Local tuning preserves the gift, the tactical trigger, and exact visible numbers.
#guard
  let p := proposal.tune 2
  p.equipment == proposal.equipment && p.requestedRules == proposal.requestedRules &&
    p.scenes.isEmpty && (p.rules.headD fury).trigger == fury.trigger &&
    (p.rules.headD fury).hitBonus == 1 && (p.rules.headD fury).damageBonus == 1 &&
    (p.rules.headD fury).description == counterDescription (p.rules.headD fury) &&
    (p.rules.getD 1 shelter) == shelter

#guard (tuneCounter 16 fury).hitBonus == 4 && (tuneCounter 16 fury).damageBonus == 6
#guard (ironSkin.tune 1).requestedRules == ironSkin.requestedRules

#guard (ironSkin.prepare shoreGame).toOption.isSome

-- Extra armor can make both sides invulnerable; legality must not ignore the new effects.
#guard
  let unarmed := { Lighthouse.mara with weapon := .punch }
  let shell : CombatRule := {
    name := "Shell", description := "Four extra armor.", side := "hero", trigger := "always", armorBonus := 4 }
  let rules : RuleSet := { combatRules := [shell, { shell with side := "foes" }] }
  decide (FightCanEnd {} unarmed unarmed) && !decide (FightCanEnd rules unarmed unarmed)

/-- A two-attempt tree instantiates the retry theorem with a real candidate and sampling law. -/
def safeRetries : RetryTree 2 :=
  .attempt TestStory.safeCandidate zeroLaw fun _ =>
    .attempt TestStory.safeCandidate zeroLaw fun _ => .stop

/-- Both histories satisfy the sampling hypotheses, rather than assuming the risk conclusion. -/
theorem safeRetries_valid : safeRetries.Valid := by
  have probabilities : ∀ i, 0 ≤ TestStory.safeCandidate.truth i ∧ TestStory.safeCandidate.truth i ≤ 1 := by
    intro i
    rw [safe_truth_zero]
    decide +kernel
  exact ⟨zeroLaw_valid, ⟨zeroLaw_sampling⟩, probabilities,
    fun _ => ⟨zeroLaw_valid, ⟨zeroLaw_sampling⟩, probabilities, fun _ => True.intro⟩⟩

example : safeRetries.falseAcceptance 0 ≤ confidenceDelta := safeRetries.fair 0 safeRetries_valid

-- A grant changes real equipment; HP, identity, attributes, purchased skills, and history stay.
#guard match proposal.prepare { shoreGame with hp := 7 } with
  | .error _ => false
  | .ok p => p.game.hero.weapon == .flamethrower && p.game.hp == 7 &&
    p.game.hero.name == shoreGame.hero.name && p.game.hero.skills == shoreGame.hero.skills &&
    p.game.hero.dx == shoreGame.hero.dx && p.game.trail == shoreGame.trail &&
    p.game.rules.weaponLevel p.game.hero == 12 &&
    (p.game.rules.weaponDice p.game.hero).count == 3

-- An active Fight retains both sides' wounds, last maneuvers, round, and order.
#guard match proposal.prepare fightGame with
  | .error _ => false
  | .ok p => match fightGame.phase, p.game.phase with
    | .fight old, .fight fresh => fresh.state.hero.being.weapon == .flamethrower &&
      fresh.state.hero.hp == old.state.hero.hp && fresh.state.hero.maneuver == old.state.hero.maneuver &&
      fresh.state.foes == old.state.foes && fresh.order == old.order && fresh.round == old.round
    | _, _ => false

/-- Fixed dice make the rule trigger and its exact extra injury observable. -/
private def fixedRoll (n : Nat) : Id (List Nat) := pure (List.replicate n 1)

-- A non-weapon request changes actual injury while leaving the weapon intact.
#guard match ironSkin.prepare shoreGame with
  | .error _ => false
  | .ok p =>
    let foe : Fighter := { being := Lighthouse.wrecker 1, hp := 10 }
    let hero : Fighter := { being := p.game.hero, hp := 11 }
    let base := (attackWith shoreGame.rules fixedRoll (some 0) foe none hero).run
    let changed := (attackWith p.game.rules fixedRoll (some 0) foe none hero).run
    changed.1 < base.1 && p.game.hero.weapon == shoreGame.hero.weapon

-- Naming one weapon does not rename an enemy's weapon or earlier fight cards.
#guard
  let gift := { flame with weapon := shoreGame.hero.weapon, name := "Singing Blade" }
  let rules := { shoreGame.rules with equipment := [gift] }
  let oldCard := shoreGame.hero.card shoreGame.rules 11
  weaponText rules shoreGame.adventure.themes shoreGame.hero == "Singing Blade" &&
    weaponText rules shoreGame.adventure.themes { shoreGame.hero with name := "Someone else" } ==
      shoreGame.adventure.themes.weapon shoreGame.hero.weapon &&
    (cardJson shoreGame.adventure.themes oldCard).getObjValD "weapon" ==
      Lean.Json.str (shoreGame.adventure.themes.weapon shoreGame.hero.weapon)

-- Fury fires only for a wounded enemy. The underlying attack still uses the shared Engine.
#guard
  let foe : Fighter := { being := Lighthouse.wrecker 1, hp := 1 }
  let hero : Fighter := { being := Lighthouse.mara, hp := 11 }
  let base := (attackWith {} fixedRoll (some 0) foe none hero).run
  let changed := (attackWith { combatRules := [fury] } fixedRoll (some 0) foe none hero).run
  changed.1 > base.1 && changed.2.contains (.worldRule fury.name fury.description) &&
    !(fury.active {} (some 0) { foe with hp := 20 } hero)

-- The same trigger does not give the Character an enemy bonus.
#guard !(fury.active {} none { being := Lighthouse.mara, hp := 1 }
  { being := Lighthouse.wrecker 1, hp := 10 })

-- Admission starts from the adventure even when the player is wounded in a later fight.
#guard match proposal.prepare { fightGame with hp := 2, trail := shoreGame.trail ++ fightGame.trail } with
  | .error _ => false
  | .ok p => p.candidate.resume.isNone && p.candidate.elapsed == 0 &&
    p.game.hp == 2 && p.game.sceneId? == fightGame.sceneId? &&
    p.candidate.hero.weapon == .flamethrower

-- Fairness prompt bands also start at turn zero, independent of the pause point.
#guard
  let later := { fightGame with hp := 2 }
  let ctx := (Lean.Json.parse (context later "Give me iron skin" (attemptRisk 0))).toOption.get!
  ctx.getObjValD "ranges" ==
    ((Lean.Json.parse (context shoreGame "Give me iron skin" (attemptRisk 0))).toOption.get!).getObjValD "ranges"

-- A missing late row and an aborted combat batch cannot be admitted.
#guard !decide (ValidationAccepted 5 ⟨#[1000,1000,1000,1000,0,0], #[0,0,0,0,0,0],1000,false⟩ (attemptRisk 0) 3)
#guard !decide (ValidationAccepted 5 ⟨#[1000,1000,1000,1000,1000,1000], #[0,0,0,0,0,0],1000,true⟩ (attemptRisk 0) 0)

/-- Play from a checkpoint with the simulator's maneuver policy and actual `step` function. -/
def finishPlayed : Nat → Game → Roll Game
  | 0, g => pure g
  | fuel+1, g => do
    match g.phase with
    | .fight f =>
      let (m, t) ← Simulation.pickManeuver f.state
      let (next, _) ← step g (.maneuver m (if m.attacks then some t else none))
      finishPlayed fuel next
    | _ => pure g

-- Resume simulation and actual play consume the same dice, without repeating early enemy turns.
#guard match proposal.prepare fightGame with
  | .error _ => false
  | .ok p => match p.game.phase with
    | .fight f => (List.range 30).all fun seed =>
      let (played, playDice) := (finishPlayed 200 p.game).run ⟨seed.toUInt64⟩
      let (simulated, simDice) := (Simulation.resumeFight p.game.rules f 200).run ⟨seed.toUInt64⟩
      match simulated with
      | none => false
      | some result => played.hp == result.hero.hp && playDice.state == simDice.state &&
        (played.phase.name == "dead") == !result.hero.alive
    | _ => false

end Rpg.WorldChange.Tests
