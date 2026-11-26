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

/-- The two bounds of `exitLaw_exact` at `n` rounds, for the results that `event` picks. -/
private def withinExactBounds (law : Distribution CombatResult) (event : CombatResult → Bool)
    (n : Nat) : Bool :=
  let p := combatProcess rules (turnOrder rules hero [foe])
  let start := fightStart rules hero 2 [foe]
  let by_n := p.eventBy (fun s => event (terminalResult s)) n start
  by_n ≤ law.mass event && law.mass event ≤ by_n + p.unfinished n start

-- The real exit law at full HP is inside the bounds of `exitLaw_exact`, for death and for a win,
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

-- Static legality and the sampled rows cannot authorize an inconsistent pause point.
#guard match proposal.prepare {pausedGame with hp := 1} with
  | .error _ => false
  | .ok p =>
    let (counts,admitted) := p.admit 1 Confidence.confidenceDelta
    counts.combatRejected && admitted.isNone

-- When a paused Fight fails its check, the author sees its own message, not the general one.
#guard
  let counts : ValidationCounts :=
    {trials := #[0, 0], deaths := #[0, 0], combatRejected := true, pausedFight := some {message := "Too large.", final := true}}
  let lines := failedRows 1 counts Confidence.confidenceDelta 0 defaultPolicy
  lines.contains "Too large." && !lines.any (·.startsWith "admission failed")
#guard
  let counts : ValidationCounts := {trials := #[0, 0], deaths := #[0, 0], combatRejected := true}
  (failedRows 1 counts Confidence.confidenceDelta 0 defaultPolicy).any (·.startsWith "admission failed")

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

end Rpg.AdmissionTests
