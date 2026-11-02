import Rpg.WorldChangePrompt
import Rpg.PlayTests
import Rpg.Probability.ConfidenceTests

/-! Regression checks for real adventure changes, their scope, and paused combat.
Large balance batches run through the compiled change-check executable. -/
namespace Rpg.WorldChange.Tests
open Probability Probability.Confidence

/-- An equipment gift retains the flamethrower's full 3d spray attack. -/
def flame : EquipmentRule :=
  ⟨"Mara", .flamethrower, "Stormglass Flamethrower", 12, 3, 0⟩

/-- Wounded enemies rally; the player can finish them before they counterattack. -/
def fury : CombatRule :=
  { name := "Scorched Fury", description := "Enemies at half HP or less gain +3 to hit and +2 damage. Finish them before they rally!",
    side := .foes, trigger := .wounded, hitBonus := 3, damageBonus := 2 }

/-- A guarded turn offers a visible way to weather the enemies' retaliation. -/
def shelter : CombatRule :=
  { name := "Cinder Veil", description := "All-Out Defense wraps you in ash: +2 armor until your next maneuver.",
    side := .hero, trigger := .guarding, armorBonus := 2 }

/-- A deterministic proposal fixture; numbers are tuned only with the screening seed. -/
def proposal : Proposal :=
  { summary := "You catch a Stormglass Flamethrower, its enchanted sight guiding your aim.",
    moment := "Wounded bandits rally through the smoke. Finish them or guard behind a Cinder Veil.",
    equipment := some flame, rules := [fury, shelter], scenes := [] }

-- A missing counter-rule, an impossible trigger, and rewritten history are rejected.
#guard !({ proposal with rules := [] }.errors roadGame).isEmpty
#guard (ruleOfJson (Lean.Json.parse "{\"name\":\"bad\",\"description\":\"bad\",\"side\":\"foes\",\"trigger\":\"heal\",\"hitBonus\":1,\"damageBonus\":0,\"armorBonus\":0}").toOption.get!).toOption.isNone
#guard !({ proposal with rules := [{ fury with trigger := .guarding }] }.errors roadGame).isEmpty
#guard !({ proposal with scenes := TestAdventure.testAdventure.scenes.take 1 }.errors roadGame).isEmpty
#guard !(proposal.errors titleGame).isEmpty
#guard !({ proposal with rules := [{ fury with trigger := .always }] }.errors roadGame).isEmpty

/-- A non-weapon request demonstrates that the same path accepts a general combat effect. -/
def ironSkin : Proposal :=
  { proposal with
    equipment := none
    requestedRules := [{
      name := "Iron Skin"
      description := "Your skin gains 2 armor."
      side := .hero, trigger := .always, armorBonus := 2 }] }

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

#guard (ironSkin.prepare roadGame).toOption.isSome

-- The Test Adventure has no loops, so it passes the short-loop check.
#guard TestAdventure.testAdventure.checkShortLoops
#guard TestAdventure.testAdventure.shortLoopErrors == []

/-- A patch that makes short loops: winning against the chief in Scene 6 goes back to Scene 5.
Scene 5 leads to Scene 6 directly, and also through Scene 10. -/
def shortLoopPatch : Proposal :=
  { proposal with scenes := [{
      id := 6, title := "Steel in the Tent", text := "The chief attacks."
      choices := [{ text := "Fight the bandit chief", outcome := .fight [TestAdventure.chief] 5 },
        { text := "Give up and run", outcome := .goto 8 }] }] }

-- The short-loop patch is rejected. The errors name the Scenes of each short loop.
#guard match shortLoopPatch.prepare roadGame with
  | .ok _ => false
  | .error errs => errs ==
    ["the loop Scene 5 -> Scene 6 -> Scene 5 has 2 steps, but a loop needs at least 4 steps: make it longer or remove it",
     "the loop Scene 5 -> Scene 10 -> Scene 6 -> Scene 5 has 3 steps, but a loop needs at least 4 steps: make it longer or remove it"]

/-- A world map for the Adventure of a game: the two places of `testMap`, and every Scene at the
first one. -/
def mapFor (g : Game) : WorldEnvironment :=
  { testMap with scenes := g.adventure.scenes.map fun s => { scene := s.id, place := 0 } }

/-- A new Ending, Scene 20, for the map tests. -/
def newEnding : Scene := { id := 20, title := "Ending: Far Away", text := "You leave.", choices := [] }

-- A change keeps the map: with no new Scene, it fits the same map.
#guard (ironSkin.prepare roadGame (some (mapFor roadGame))).toOption.isSome
-- A new Scene with no place on the map is refused, and the error names the Scene.
#guard match ({ ironSkin with scenes := [newEnding] }.prepare roadGame (some (mapFor roadGame))) with
  | .error errs => errs.contains "environment: Scene 20 needs exactly one place"
  | .ok _ => false
-- With a place, the map check passes. The new map has the old places and the new Scene.
#guard
  let p := { ironSkin with scenes := [newEnding], scenePlaces := [{ scene := 20, place := 1 }] }
  let after := p.map (mapFor roadGame)
  ((after.errors (p.story roadGame)).isEmpty && after.places == testMap.places &&
    after.scenes.length == roadGame.adventure.scenes.length + 1 : Bool)

-- The short-loop rule also runs when the Adventure has a world map.
#guard match shortLoopPatch.prepare roadGame (some (mapFor roadGame)) with
  | .ok _ => false
  | .error errs => errs.any (·.startsWith "the loop Scene 5 -> Scene 6 -> Scene 5 has 2 steps")

-- Extra armor can make both sides invulnerable; legality must not ignore the new effects.
#guard
  let unarmed := { TestAdventure.mara with weapon := .punch }
  let shell : CombatRule := {
    name := "Shell", description := "Four extra armor.", side := .hero, trigger := .always, armorBonus := 4 }
  let rules : RuleSet := { combatRules := [shell, { shell with side := .foes }] }
  decide (DamagePossible {} unarmed unarmed) && !decide (DamagePossible rules unarmed unarmed)

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

example : safeRetries.falseAcceptance 0 ≤ confidenceDelta := safeRetries.balanced 0 safeRetries_valid

-- A grant changes real equipment; HP, identity, attributes, purchased skills, and history stay.
#guard match proposal.prepare { roadGame with hp := 7 } with
  | .error _ => false
  | .ok p => p.game.hero.weapon == .flamethrower && p.game.hp == 7 &&
    p.game.hero.name == roadGame.hero.name && p.game.hero.skills == roadGame.hero.skills &&
    p.game.hero.dx == roadGame.hero.dx && p.game.trail == roadGame.trail &&
    p.game.rules.weaponLevel true p.game.hero == 12 &&
    (p.game.rules.weaponDice true p.game.hero).count == 3

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
#guard match ironSkin.prepare roadGame with
  | .error _ => false
  | .ok p =>
    let foe : Fighter := { being := TestAdventure.bandit 1, hp := 10 }
    let hero : Fighter := { being := p.game.hero, hp := 11 }
    let base := (attackWith roadGame.rules fixedRoll (some 0) foe none hero).run
    let changed := (attackWith p.game.rules fixedRoll (some 0) foe none hero).run
    changed.1 < base.1 && p.game.hero.weapon == roadGame.hero.weapon

-- Naming one weapon does not rename an enemy's weapon or earlier fight cards.
#guard
  let gift := { flame with weapon := roadGame.hero.weapon, name := "Singing Blade" }
  let rules := { roadGame.rules with equipment := [gift] }
  let oldCard := roadGame.hero.card roadGame.rules true 11
  weaponText rules roadGame.adventure.themes true roadGame.hero == "Singing Blade" &&
    weaponText rules roadGame.adventure.themes false { roadGame.hero with name := "Someone else" } ==
      roadGame.adventure.themes.weapon roadGame.hero.weapon &&
    (cardJson roadGame.adventure.themes oldCard).getObjValD "weapon" ==
      Lean.Json.str (roadGame.adventure.themes.weapon roadGame.hero.weapon)

-- A namesake enemy never receives the hero's equipment, including its attack and damage.
#guard
  let namesake := { TestAdventure.mara with weapon := .flamethrower }
  let rules : RuleSet := { equipment := [flame] }
  rules.equipmentFor true namesake == some flame &&
    (rules.equipmentFor false namesake).isNone &&
    rules.weaponLevel false namesake == rules.attackLevel namesake &&
    rules.weaponDice false namesake == rules.damage namesake.weapon namesake.st

-- The actual attack function also keeps a namesake foe on its ordinary weapon profile.
#guard
  let namesake : Fighter := { being := { TestAdventure.mara with weapon := .flamethrower }, hp := 11 }
  let target : Fighter := { being := TestAdventure.bandit 1, hp := 10 }
  let gift := { flame with attackLevel := 18, dice := 6 }
  let rules : RuleSet := { equipment := [gift] }
  (attackWith rules fixedRoll (some 0) namesake none target).run ==
    (attackWith {} fixedRoll (some 0) namesake none target).run &&
    (attackWith rules fixedRoll none namesake (some 0) target).run !=
      (attackWith {} fixedRoll none namesake (some 0) target).run

-- Fury fires only for a wounded enemy. The underlying attack still uses the shared Engine.
#guard
  let foe : Fighter := { being := TestAdventure.bandit 1, hp := 1 }
  let hero : Fighter := { being := TestAdventure.mara, hp := 11 }
  let base := (attackWith {} fixedRoll (some 0) foe none hero).run
  let changed := (attackWith { combatRules := [fury] } fixedRoll (some 0) foe none hero).run
  changed.1 > base.1 && changed.2.contains (.worldRule fury.name fury.description) &&
    !(fury.active {} (some 0) { foe with hp := 20 } hero)

-- The same trigger does not give the Character an enemy bonus.
#guard !(fury.active {} none { being := TestAdventure.mara, hp := 1 }
  { being := TestAdventure.bandit 1, hp := 10 })

-- Admission starts from the adventure even when the player is wounded in a later fight.
#guard match proposal.prepare { fightGame with hp := 2, trail := roadGame.trail ++ fightGame.trail } with
  | .error _ => false
  | .ok p => p.candidate.resume.isNone && p.candidate.elapsed == 0 &&
    p.game.hp == 2 && p.game.sceneId? == fightGame.sceneId? &&
    p.candidate.hero.weapon == .flamethrower

-- The balance bands in the prompt also start at turn zero, independent of the pause point.
#guard
  let later := { fightGame with hp := 2 }
  let ctx := (Lean.Json.parse (context later "Give me iron skin" (attemptRisk 0))).toOption.get!
  ctx.getObjValD "ranges" ==
    ((Lean.Json.parse (context roadGame "Give me iron skin" (attemptRisk 0))).toOption.get!).getObjValD "ranges"

-- A missing late row and an aborted combat batch cannot be admitted.
#guard !decide (ValidationAccepted 5 ⟨#[1200,1200,1200,1200,0,0], #[0,0,0,0,0,0],1200,false,false⟩ (attemptRisk 0) 3
  defaultPolicy)
#guard !decide (ValidationAccepted 5 ⟨#[1200,1200,1200,1200,1200,1200], #[0,0,0,0,0,0],1200,true,false⟩ (attemptRisk 0) 0
  defaultPolicy)

/-- A policy that is not the default, only to test that a change keeps the policy of its game. -/
def otherPolicy : BalancePolicy := ⟨9 / 10, 2, 1 / 10⟩

/-- The road checkpoint, with `otherPolicy`. -/
def otherRoad : Game := { roadGame with policy := otherPolicy }

-- A change is checked against the policy of its game, and the changed game keeps that policy.
#guard match proposal.prepare otherRoad with
  | .error _ => false
  | .ok p => p.candidate.policy == otherPolicy &&
    p.game.policy == otherPolicy &&
    (List.finRange (liveHorizon + 1)).all fun i =>
      let band := confidenceBandsFor otherPolicy liveHorizon i
      (p.candidate.bands i).target == band.target && (p.candidate.bands i).tolerance == band.tolerance

-- A proposal cannot pick another policy: a `difficulty` field in its JSON is not read.
#guard
  let text := (Lean.Json.mkObj [
    ("supported", true), ("summary", proposal.summary), ("moment", proposal.moment),
    ("equipment", equipmentJson flame), ("requestedRules", Lean.Json.arr #[]),
    ("rules", Lean.toJson (proposal.rules.map ruleJson)), ("scenes", Lean.Json.arr #[]),
    ("difficulty", "easy")]).compress
  match Proposal.parse "Mara" text with
  | .error _ => false
  | .ok q => match q.prepare otherRoad with
    | .error _ => false
    | .ok p => p.game.policy == otherPolicy && p.candidate.policy == otherPolicy

-- The Dungeon Master gets the bands of the game's own policy.
#guard
  let ranges (g : Game) := ((Lean.Json.parse (context g "Give me iron skin" (attemptRisk 0))).toOption.get!).getObjValD "ranges"
  ranges otherRoad != ranges roadGame &&
    ranges otherRoad == ranges { otherRoad with phase := fightGame.phase }

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
