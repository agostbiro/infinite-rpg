import Rpg.WorldChange
import Rpg.HPInvariant
import Rpg.Probability.TestStory

namespace Rpg.AdmissionTests
open Probability

private def hero : Being :=
  {name := "Hero", st := 1, dx := 10, iq := 10, ht := 10,
    skills := [(.broadsword,12)], weapon := .broadsword, armor := .none}

private def foe : Being := {hero with name := "Foe"}

private def rules : RuleSet :=
  {maxHP := fun _ => 2, minST := fun _ => 0, points := fun _ => 0,
    characterPoints := 0, characterAttributeMin := 1, injury := fun _ _ _ => 100}

private def story : Adventure :=
  {title := "Certification fixture", start := 0, scenes := [
    {id := 0, title := "Fight", text := "", choices := [{text := "Fight", outcome := .fight [foe] 1}]},
    {id := 1, title := "End", text := "", choices := []}]}

private def definition : AdventureDefinition :=
  ⟨rules,hero,checkCharacter_sound (by decide),story,check_sound (by decide)⟩

-- At least one initial HP is mandatory, even for an otherwise legal custom character.
example : checkCharacter {rules with maxHP := fun _ => 0} hero ≠ [] := by decide +kernel

-- Lethal injuries mean the full-HP search never visits the one-HP entry state.
-- A certificate for full HP alone therefore cannot replace encounter-wide admission.
#guard
  let start := fightStart rules hero 2 [foe]
  let (_,cache) := (solveCombatAnswer (fastRound rules (turnOrder rules hero [foe])) start).run {}
  !(decide ((CombatWitness.mk cache).contains (fightStart rules hero 1 [foe])))

#guard (certifyEncounter rules hero [foe]).isSome
-- The exit law at each entry HP is a probability law with no weight on `stalled`, and a
-- Character who enters with 0 HP is already dead.
#guard match certifyEncounter rules hero [foe] with
  | some c => (List.range (rules.maxHP hero + 1)).all (fun hp => match c.exitLaw? hp with
      | some law => law.mass (fun _ => true) == 1 && law.mass (· == .stalled) == 0
      | none => false) &&
      (c.exitLaw? 0).map (·.mass (· == .died)) == some 1 &&
      -- An entry HP above full HP was not checked, so it has no exit law.
      (c.exitLaw? (rules.maxHP hero + 1)).isNone
  | none => false
#guard (certifyAdventureCombat definition).isSome

/-- The two bounds of `exitLaw_bounds` at `n` rounds, for the results that `event` picks. -/
private def withinExactBounds (law : Distribution CombatResult) (event : CombatResult → Bool)
    (n : Nat) : Bool :=
  let p := combatProcess rules (turnOrder rules hero [foe])
  let start := fightStart rules hero 2 [foe]
  let by_n := p.eventBy (fun s => event (terminalResult s)) n start
  by_n ≤ law.mass event && law.mass event ≤ by_n + p.unfinished n start

-- The real exit law at full HP is inside the bounds of `exitLaw_bounds`, for death and for a win,
-- after 1, 2 and 3 rounds of the spec process.
#guard match certifyEncounter rules hero [foe] with
  | some c => match c.exitLaw? 2 with
    | some law => [1, 2, 3].all fun n =>
        withinExactBounds law (· == .died) n && withinExactBounds law (· matches .won _) n
    | none => false
  | none => false

-- The bounds reject a wrong exit law: a sure win breaks the lower bound for death, because the
-- Character can die in the first round.
#guard !withinExactBounds (pure (.won 2)) (· == .died) 1

-- The premises of `exitLaw_bounds` hold on this fixture. A certificate exists: the `#guard` on
-- `certifyEncounter` above shows it in compiled code. The kernel cannot check a witness with
-- entries, because the witness is a `Std.HashMap` and the hash of a `FightState` uses `mixHash`,
-- which the kernel cannot reduce. The entry HP 2 is full HP, and `decide` shows it.
example (c : CertifiedEncounter rules hero [foe]) :
    (combatProcess rules (turnOrder rules hero [foe])).eventBy
      (fun s => terminalResult s == .died) 1 (fightStart rules hero 2 [foe]) ≤
      (c.exitLaw 2 (by decide)).mass (· == .died) :=
  (c.exitLaw_bounds 2 (by decide) (· == .died) 1).1

/-- The test rules, with 0 HP for every Being, so each Fight is over at its start. -/
private def zeroRules : RuleSet := {rules with maxHP := fun _ => 0}

/-- A certificate for the Fight against `foe` under `zeroRules` that the kernel checks. The only
entry HP is 0, so the start is over, and the empty witness needs no rows. -/
private def zeroEncounter : CertifiedEncounter zeroRules hero [foe] where
  witness := ⟨{}⟩
  starts := by decide
  rows := by simp [CombatWitness.states]

-- Every premise of `exitLaw_exact` holds on a concrete certificate, entry HP and allowance.
example : ∃ N : Nat, ∀ n, N ≤ n →
    (combatProcess zeroRules (turnOrder zeroRules hero [foe])).eventBy
      (fun s => terminalResult s == .died) n (fightStart zeroRules hero 0 [foe]) ≤
      (zeroEncounter.exitLaw 0 (by decide)).mass (· == .died) ∧
    (zeroEncounter.exitLaw 0 (by decide)).mass (· == .died) ≤
      (combatProcess zeroRules (turnOrder zeroRules hero [foe])).eventBy
        (fun s => terminalResult s == .died) n (fightStart zeroRules hero 0 [foe]) + 1/2 :=
  zeroEncounter.exitLaw_exact 0 (by decide) (· == .died) (1/2) (by decide +kernel)

-- The exit law of this Fight is a sure death: the Character enters with 0 HP.
example : (zeroEncounter.exitLaw 0 (by decide)).mass (· == .died) = 1 := by decide +kernel

-- The bounds reject a wrong exit law: a sure win breaks the lower bound for death at 0 rounds.
example : ¬ ((combatProcess zeroRules (turnOrder zeroRules hero [foe])).eventBy
    (fun s => terminalResult s == .died) 0 (fightStart zeroRules hero 0 [foe]) ≤
    (pure (CombatResult.won 0) : Distribution CombatResult).mass (· == .died)) := by decide +kernel

-- End-to-end positive admission includes a real stochastic fight. Seven safe
-- choices keep its first-turn risk inside the fixed horizon-one policy band.
private def admissionStory : Adventure :=
  {story with scenes := [
    {id := 0, title := "Choice", text := "", choices :=
      {text := "Fight", outcome := .fight [foe] 1} ::
      List.replicate 7 {text := "Leave", outcome := .goto 1}},
    {id := 1, title := "End", text := "", choices := []}]}

private def admissionDefinition : AdventureDefinition :=
  ⟨rules,hero,checkCharacter_sound (by decide),admissionStory,check_sound (by decide)⟩

private def candidate : StatisticalCandidate :=
  {toAdventureDefinition := admissionDefinition, horizon := 1, horizonPositive := by decide}

#guard (admitWithSeed candidate 1).2.isSome
#guard ((admitWithSeed candidate 1).2.bind certify).isSome

-- A nonmonotone custom success rule defeats the old static damage argument:
-- positive bonuses disable every actual attack, although the static screen passes.
private def trickRules : RuleSet :=
  {rules with
    successRoll := fun level _ => if level = 12 then .criticalSuccess else .failure
    combatRules := [
      {name := "Hero bonus", description := "One to hit", side := .hero, trigger := .always, hitBonus := 1},
      {name := "Enemy bonus", description := "One to hit", side := .foes, trigger := .always, hitBonus := 1}]}

example : DamagePossible trickRules hero foe := by decide +kernel
example : check trickRules hero story = [] := by decide +kernel
#guard (certifyEncounter trickRules hero [foe]).isNone

-- A fabricated runtime scene is rejected even though the stored adventure remains legal.
private def badGame : Game := {Game.new definition with phase := .scene 999}
#guard !decide badGame.WellFormed
#guard decide (Game.new definition).WellFormed
#guard decide (((step (Game.new definition) .begin).run' ⟨7⟩).1.WellFormed)

-- The real partial-round entry point, including a wounded hero, is independently certified.
#guard (certifyContinuation rules
  {scene := 0, choice := 0, onWin := 1, order := turnOrder rules hero [foe], round := 2,
    state := fightStart rules hero 1 [foe]}).isSome

-- Admission is tied to the original starting point; continuation analysis is separate.
#guard (admitWithSeed {TestStory.safeCandidate with resume := some (.scene 0 1)} 1).2.isNone

-- Exercise the complete live-change gate, including runtime checks, without an expensive large
-- encounter.
private def liveStory : Adventure :=
  {title := "Live certification fixture", start := 0, scenes := (List.range 7).map fun i =>
    {id := i, title := "Scene", text := "", choices :=
      if i = 6 then [] else if i < 2 then [{text := "Go", outcome := .goto (i+1)}]
      else [{text := "Fight", outcome := .fight [foe] (i+1)},
            {text := "Fight", outcome := .fight [foe] (i+1)},
            {text := "Fight", outcome := .fight [foe] (i+1)},
            {text := "Go", outcome := .goto (i+1)}]}}

private def liveDefinition : AdventureDefinition :=
  ⟨rules,hero,checkCharacter_sound (by decide),liveStory,check_sound (by decide)⟩

private def liveGame := ((step (Game.new liveDefinition) .begin).run' ⟨7⟩).1

private def proposal : WorldChange.Proposal :=
  {summary := "Stronger attacks", moment := "The fighters change their tactics", equipment := none,
    requestedRules := [{name := "Bold", description := "Stronger all-out attacks", side := .hero, trigger := .reckless, hitBonus := 1}],
    rules := [{name := "Guard pressure", description := "Enemies press guarding heroes", side := .foes, trigger := .againstGuarding, hitBonus := 1}], scenes := []}

#guard match proposal.prepare liveGame with
  | .error _ => false
  | .ok p => (p.admit 1 Confidence.confidenceDelta).2.isSome

private def pausedGame : Game :=
  {liveGame with phase := .fight {
    scene := 2
    choice := 0
    onWin := 3
    order := turnOrder rules hero [foe]
    round := 2
    state := fightStart rules hero 2 [foe]}}

#guard match proposal.prepare pausedGame with
  | .error _ => false
  | .ok p => (p.admit 1 Confidence.confidenceDelta).2.isSome

-- The paused Fight passes its own check, which the server runs before it spends a validation.
#guard match proposal.prepare pausedGame with
  | .error _ => false
  | .ok p => p.checkPaused.toOption.isSome

-- Static legality and the sampled rows cannot authorize an inconsistent pause point.
#guard match proposal.prepare {pausedGame with hp := 1} with
  | .error _ => false
  | .ok p =>
    let (counts,admitted) := p.admit 1 Confidence.confidenceDelta
    counts.combatRejected && admitted.isNone

-- When a paused Fight fails its check, the author sees its own message, not the general one.
#guard
  let counts : ValidationCounts :=
    {trials := #[0, 0], deaths := #[0, 0], combatRejected := true, pausedFight := some "Too large."}
  let lines := failedRows 1 counts Confidence.confidenceDelta 0 defaultPolicy
  lines.contains "Too large." && !lines.any (·.startsWith "admission failed")
#guard
  let counts : ValidationCounts := {trials := #[0, 0], deaths := #[0, 0], combatRejected := true}
  (failedRows 1 counts Confidence.confidenceDelta 0 defaultPolicy).any (·.startsWith "admission failed")

/-- A Being with 4 HP and a broadsword, for the paused-Fight reports. -/
private def brawler (name : String) : Being :=
  {name, st := 4, dx := 10, iq := 10, ht := 10, skills := [(.broadsword, 12)],
    weapon := .broadsword, armor := .none}

/-- A paused Fight of a brawler against two others. -/
private def brawlState : FightState :=
  {hero := {being := brawler "Hero", hp := 4},
   foes := [{being := brawler "A", hp := 4}, {being := brawler "B", hp := 4}]}

/-- The paused Fight of `brawlState`. -/
private def brawl : FightPhase :=
  {scene := 0, choice := 0, onWin := 1, round := 1, state := brawlState,
   order := turnOrder {} (brawler "Hero") [brawler "A", brawler "B"]}

/-- A counter-rule that gives the Creatures +6 damage. -/
private def furyRule : CombatRule :=
  {name := "Fury", description := "+6 damage.", side := .foes, trigger := .always, damageBonus := 6}

/-- Rules with the counter-rule `furyRule`. -/
private def fury : RuleSet := {combatRules := [furyRule]}

-- A counter-rule changes the size of a round in either direction, so no size failure of a
-- paused Fight is final. Here +6 damage for the Creatures raises the round bound from 525 to 833.
#guard roundSizeBound brawl.order (attackBounds {} brawl.state) brawl.state == 525 &&
  roundSizeBound brawl.order (attackBounds fury brawl.state) brawl.state == 833
-- The message for a round that is too large asks for a revision of the counter-rules.
#guard match checkContinuation fury brawl {roundEntries := 600} with
  | .error e => e == .roundTooLarge && ((e.message brawl).splitOn "Revise them").length == 2
  | .ok _ => false

-- Static legality and a passing sampled batch do not admit a short cycle.
private def loopStory : Adventure :=
  {story with scenes := [
    {id := 0, title := "Loop", text := "", choices := [
      {text := "Again", outcome := .goto 0}, {text := "Leave", outcome := .goto 1}]},
    {id := 1, title := "End", text := "", choices := []}]}

private def loopDefinition : AdventureDefinition :=
  ⟨rules, hero, checkCharacter_sound (by decide), loopStory, check_sound (by decide)⟩

private def loopCandidate : StatisticalCandidate :=
  {toAdventureDefinition := loopDefinition, horizon := 1, horizonPositive := by decide}

#guard decide (ValidationAccepted 1 (sampleCounts loopCandidate 1 validationGames)
  Confidence.confidenceDelta 0 defaultPolicy)
#guard (admitWithSeed loopCandidate 1).2.isNone

-- A certified Adventure necessarily supplies the probability theorem.
example (a : CertifiedAdventure) (foes : List Being) (hf : foes ∈ encounterFoes a.admitted.candidate.story)
    (hp : Int) (lo : 0 ≤ hp) (hi : hp ≤ a.admitted.candidate.rules.maxHP a.admitted.candidate.hero) :
    (combatProcess a.admitted.candidate.rules
      (turnOrder a.admitted.candidate.rules a.admitted.candidate.hero foes)).AlmostSurelyTerminates
      (fightStart a.admitted.candidate.rules a.admitted.candidate.hero hp foes) :=
  a.combat.ends_almostSurely foes hf hp lo hi

-- A Fight whose starts alone are over the state limit is rejected before they are made: 20,001
-- entry HP from 1 up give 60,003 states, above the limit of 60,000.
#guard (certifyEncounter {rules with maxHP := fun b => if b.name = "Hero" then 20001 else 2}
  hero [foe]).isNone
-- The early rejection needs a living Creature. With none, every start has ended, and the Fight
-- is certified.
#guard (certifyEncounter {rules with maxHP := fun b => if b.name = "Hero" then 20001 else 0}
  hero [foe]).isSome

end Rpg.AdmissionTests
