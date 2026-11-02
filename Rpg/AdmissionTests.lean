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
  let (_,cache) := (solveCombatAnswer rules heroPolicy (turnOrder rules hero [foe]) start).run []
  !(decide ((CombatWitness.mk cache).contains (fightStart rules hero 1 [foe])))

#guard (certifyEncounter rules hero [foe]).isSome
#guard (certifyAdventureCombat definition).isSome

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

-- Exercise the complete live-change gate, including runtime checks and the
-- mandatory adventure certificate, without an expensive large encounter.
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
  {liveGame with
    trail := [{source := 0, choice := 0, target := 1, rolled := none},
      {source := 1, choice := 0, target := 2, rolled := none}]
    phase := .fight {
    scene := 2
    choice := 0
    onWin := 3
    order := turnOrder rules hero [foe]
    round := 2
    state := fightStart rules hero 2 [foe]}}

-- This short fixture passed from time zero but ends too early for the aged window.
-- Its combat remains certifiable; the checkpoint balance gate must reject it.
#guard match proposal.prepare pausedGame with
  | .error _ => false
  | .ok p =>
    let (counts, admitted) := p.admit 1 Confidence.confidenceDelta
    admitted.isNone && !counts.combatRejected && decide p.game.WellFormed &&
      (certifyAdventureCombat p.definition).isSome &&
      match p.game.phase with
      | .fight f => (certifyContinuation p.game.rules f).isSome
      | _ => false

-- Static legality and the sampled rows cannot authorize an inconsistent pause point.
#guard match proposal.prepare {pausedGame with hp := 1} with
  | .error errors => errors.contains "The checkpoint HP does not match the paused Fight."
  | .ok p =>
    let (counts,admitted) := p.admit 1 Confidence.confidenceDelta
    counts.combatRejected && admitted.isNone

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

-- A public admitted value necessarily supplies the probability theorem.
example (a : StatisticalAdventure) (foes : List Being) (hf : foes ∈ encounterFoes a.candidate.story)
    (hp : Int) (lo : 0 ≤ hp) (hi : hp ≤ a.candidate.rules.maxHP a.candidate.hero) :
    (combatProcess a.candidate.rules (turnOrder a.candidate.rules a.candidate.hero foes)).AlmostSurelyTerminates
      (fightStart a.candidate.rules a.candidate.hero hp foes) :=
  a.combat.ends_almostSurely foes hf hp lo hi

end Rpg.AdmissionTests
