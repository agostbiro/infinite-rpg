import Rpg.Live
import Rpg.Probability.Retry
import Rpg.Probability.Screening
import Rpg.Probability.ContinuationCertificate
import Rpg.RuntimeInvariant

/-! In-play changes are checked data, not generated executable code. An accepted
patch keeps the checkpoint, HP, history, core rules, and balance policy. Admission samples the
updated adventure from that checkpoint, at the original curve's elapsed age, before the server can
install it. A proposal has no policy field, so it cannot change the difficulty level. -/
namespace Rpg.WorldChange
open Lean Probability Probability.Confidence

/-- A GM proposal can change gameplay, scenery, or both. -/
structure Proposal where
  summary : String
  moment : String
  equipment : Option EquipmentRule
  /-- The requested effects stay fixed while the GM balances its counter-rules. -/
  requestedRules : List CombatRule := []
  rules : List CombatRule
  scenes : List Scene
  /-- The place on the world map of each new Scene. The map itself does not change. -/
  scenePlaces : List ScenePlace := []
  environment : Option WorldEnvironment := none
  supported : Bool := true

/-- A tuned effect's description states its actual condition and numbers. -/
def counterDescription (r : CombatRule) : String :=
  let trigger := match r.trigger with
    | .wounded => "at half HP or less"
    | .desperate => "at one third HP or less"
    | .reckless => "after choosing All-Out Attack"
    | .guarding => "after choosing All-Out Defense"
    | .againstReckless => "against an opponent using All-Out Attack"
    | .againstGuarding => "against an opponent using All-Out Defense"
    | .againstFlame => "against an opponent wielding a flamethrower"
    | .always => "always"
  let effects := (if r.hitBonus = 0 then [] else [s!"{r.hitBonus} to hit"]) ++
    (if r.damageBonus = 0 then [] else [s!"{r.damageBonus} damage"]) ++
    (if r.armorBonus = 0 then [] else [s!"{r.armorBonus} extra armor"])
  s!"{if r.side == .foes then "Enemies" else "You"} gain {String.intercalate ", " effects} {trigger}."

/-- Scale only positive enemy counter-effects; keep the named tactical trigger and all gifts. -/
def tuneCounter (quarters : Nat) (r : CombatRule) : CombatRule :=
  if r.side != .foes then r else
  let scale (n cap : Nat) := if n = 0 then 0 else min cap (max 1 (n * quarters / 4))
  let tuned := { r with
    hitBonus := if r.hitBonus > 0 then (scale r.hitBonus.toNat 4 : Int) else r.hitBonus,
    damageBonus := if r.damageBonus > 0 then (scale r.damageBonus.toNat 6 : Int) else r.damageBonus,
    armorBonus := scale r.armorBonus 4 }
  if tuned == r then r else { tuned with description := counterDescription tuned }

/-- Local exploratory variants avoid another GM request for a numerical counter adjustment. -/
def Proposal.tune (p : Proposal) (quarters : Nat) : Proposal :=
  { p with rules := p.rules.map (tuneCounter quarters) }

/-- Local balancing cannot weaken the requested mechanic or rewrite scenes. -/
theorem Proposal.tune_preserves_request (p : Proposal) (quarters : Nat) :
    (p.tune quarters).equipment = p.equipment ∧
    (p.tune quarters).requestedRules = p.requestedRules ∧
    (p.tune quarters).scenes = p.scenes := ⟨rfl, rfl, rfl⟩

/-- Read a combat rule; unknown fields cannot modify the core rules. -/
def ruleOfJson (j : Json) : Except String CombatRule := do
  return {
    name := ← j.getObjValAs? String "name"
    description := ← j.getObjValAs? String "description"
    side := ← ofKey? CombatSide.all CombatSide.key "side" (← j.getObjValAs? String "side")
    trigger := ← ofKey? CombatTrigger.all CombatTrigger.key "trigger" (← j.getObjValAs? String "trigger")
    hitBonus := ← j.getObjValAs? Int "hitBonus"
    damageBonus := ← j.getObjValAs? Int "damageBonus"
    armorBonus := ← j.getObjValAs? Nat "armorBonus" }

/-- The server fixes the equipment owner to the current Character. -/
def equipmentOfJson (owner : String) (j : Json) : Except String EquipmentRule := do
  return {
    owner
    weapon := ← ofKey? Weapon.all Weapon.key "weapon" (← j.getObjValAs? String "weapon")
    name := ← j.getObjValAs? String "name"
    attackLevel := ← j.getObjValAs? Nat "attackLevel"
    dice := ← j.getObjValAs? Nat "dice"
    add := ← j.getObjValAs? Int "add" }

/-- Parse a proposal without executing any of its text. -/
def Proposal.parse (owner text : String) : Except String Proposal := do
  let j ← Json.parse text
  let equipment ← j.getObjVal? "equipment"
  let gear ← if equipment == Json.null then pure none else some <$> equipmentOfJson owner equipment
  let environment ← match j.getObjVal? "environment" with
    | .error _ => pure none
    | .ok value => fromJson? (α := Option WorldEnvironment) value
  return {
    environment
    summary := ← j.getObjValAs? String "summary"
    moment := ← j.getObjValAs? String "moment"
    equipment := gear
    requestedRules := ← listField j "requestedRules" ruleOfJson
    rules := ← listField j "rules" ruleOfJson
    scenes := ← listField j "scenes" sceneOfJson
    scenePlaces := ← optListField j "scenePlaces" fun x => fromJson? x
    supported := ← j.getObjValAs? Bool "supported" }

/-- A live change can be requested between choices or on the Character's combat turn. -/
def available (g : Game) : Bool := match g.phase with
  | .scene _ => g.hp > 0
  | .fight f => !f.state.over
  | _ => false

/-- Limits keep proposals meaningful, bounded, and inside the supported adventure language. -/
def Proposal.errors (p : Proposal) (g : Game) : List String :=
  (if p.supported then [] else ["This requested behavior is outside the supported adventure rules."]) ++
  (if available g then [] else ["A change needs a living Character in a Scene or Fight."]) ++
  (if p.summary.isEmpty || p.moment.isEmpty then ["Describe the change and its dramatic player moment."] else []) ++
  (if p.equipment.isNone && p.requestedRules.isEmpty && p.rules.isEmpty && p.scenes.isEmpty && p.environment.isNone && p.scenePlaces.isEmpty then
    ["The proposal must implement the requested change, separately from the counter-rules."] else []) ++
  tooLong "the change summary" 800 p.summary ++ tooLong "the dramatic moment" 800 p.moment ++
  (if g.rules.combatRules.length + p.requestedRules.length + p.rules.length > 24 then ["At most 24 adventure effects can be active."] else []) ++
  (p.requestedRules ++ p.rules).flatMap (fun r =>
    (if r.name.isEmpty || r.description.isEmpty then ["Every rule needs a name and description."] else []) ++
    tooLong "a rule name" 80 r.name ++ tooLong "a rule description" 400 r.description ++
    (if r.side == .foes && [.reckless, .guarding].contains r.trigger then
      [s!"{r.name} cannot fire: enemies always choose Attack."] else []) ++
    (if r.hitBonus < -4 || r.hitBonus > 4 || r.damageBonus < -4 || r.damageBonus > 6 || r.armorBonus > 4 then
      [s!"{r.name}: hit bonus must be -4..4, damage -4..6, armor 0..4."] else []) ++
    (if r.hitBonus == 0 && r.damageBonus == 0 && r.armorBonus == 0 then
      [s!"{r.name} must have an actual effect."] else []) ++
    (if g.rules.combatRules.any (fun old => old.name == r.name) then
      [s!"{r.name} already exists; keep earlier changes."] else [])) ++
  (if ((p.requestedRules ++ p.rules).map (·.name)).eraseDups.length != p.requestedRules.length + p.rules.length then
    ["Rule names must be distinct."] else []) ++
  (match p.equipment with
    | none => []
    | some e =>
      tooLong "the equipment name" 80 e.name ++
      (if e.name.isEmpty || e.owner != g.hero.name || e.attackLevel < 3 || e.attackLevel > 18 ||
        e.dice < 1 || e.dice > 6 || e.add < -3 || e.add > 6 then
        ["Equipment needs a name, attack level 3..18, 1..6 damage dice, and add -3..6."] else [])) ++
  (if p.scenes.length > maxScenes then ["Too many scene patches."] else []) ++
  (if (p.scenes.map (·.id)).eraseDups.length != p.scenes.length then ["Scene patches must have distinct IDs."] else []) ++
  p.scenes.flatMap (fun sc =>
    (if sc.choices.length > 8 then [s!"Scene {sc.id} has more than 8 Choices."] else []) ++
    sc.choices.filterMap (fun ch => if ch.outcome.foes.length > 4 then
      some "A new Fight can have at most 4 Creatures." else none))

/-- A patch changes only two adventure-local data fields of the current rules. -/
def Proposal.ruleSet (p : Proposal) (g : Game) : RuleSet :=
  { g.rules with
    equipment := match p.equipment with
      | none => g.rules.equipment
      | some e => e :: g.rules.equipment.filter (fun old => old.owner != g.hero.name),
    combatRules := g.rules.combatRules ++ p.requestedRules ++ p.rules }

/-- Install or append future scenes, retaining every untouched scene. -/
def Proposal.story (p : Proposal) (g : Game) : Adventure :=
  let scenes := g.adventure.scenes.map fun sc => (p.scenes.find? (·.id == sc.id)).getD sc
  let added := p.scenes.filter fun sc => (g.adventure.scene? sc.id).isNone
  { g.adventure with scenes := scenes ++ added }

/-- Replace the environment when supplied and upsert scene placements. -/
def Proposal.map (p : Proposal) (old : WorldEnvironment) : WorldEnvironment :=
  let e := p.environment.getD old
  { e with scenes := e.scenes.filter (fun sc => !(p.scenePlaces.any (·.scene == sc.scene))) ++ p.scenePlaces }

/-- Resolve the proposed environment even when the old world has no map. -/
def Proposal.environmentAfter (p : Proposal) (old : Option WorldEnvironment) : Option WorldEnvironment :=
  (p.environment.or old).map p.map

/-- Scenery alone cannot change any game rule or graph edge. -/
def Proposal.visualOnly (p : Proposal) : Prop :=
  p.equipment = none ∧ p.requestedRules = [] ∧ p.rules = [] ∧ p.scenes = []

instance (p : Proposal) : Decidable p.visualOnly := by unfold Proposal.visualOnly; infer_instance

/-- The exact gameplay data is unchanged by a scenery-only proposal. -/
theorem Proposal.visualOnly_preserves (p : Proposal) (g : Game) (h : p.visualOnly) :
    p.ruleSet g = g.rules ∧ p.story g = g.adventure := by
  rcases h with ⟨equipment, requested, rules, scenes⟩
  simp [ruleSet, story, equipment, requested, rules, scenes]

/-- The visible HP and the paused combat HP must name the same checkpoint. -/
def checkpointConsistent (g : Game) : Prop :=
  match g.phase with
  | .fight f => g.hp = f.state.hero.hp
  | _ => True

instance (g : Game) : Decidable (checkpointConsistent g) := by
  unfold checkpointConsistent
  split <;> infer_instance

/-- Event scenes cannot be edited while a fight is running. -/
def Proposal.graphStableInFight (p : Proposal) (g : Game) : Prop :=
  match g.phase with
  | .fight _ => p.scenes = []
  | _ => True

instance (p : Proposal) (g : Game) : Decidable (p.graphStableInFight g) := by
  unfold Proposal.graphStableInFight
  split <;> infer_instance

/-- A prepared change carries the legality proofs, but cannot yet be installed. -/
structure Prepared where
  before : Game
  proposal : Proposal
  proposalValid : proposal.errors before = []
  policyValid : before.policy.Valid
  checkpointValid : checkpointConsistent before
  graphStable : proposal.graphStableInFight before
  heroLegal : LegalCharacter (proposal.ruleSet before)
    { before.hero with weapon := proposal.equipment.map (·.weapon) |>.getD before.hero.weapon }
  noShortLoops : (proposal.story before).NoShortLoops
  storyLegal : LegalAdventure (proposal.ruleSet before)
    { before.hero with weapon := proposal.equipment.map (·.weapon) |>.getD before.hero.weapon }
    (proposal.story before)

/-- The new definition preserves the Character's identity, attributes, skills, and armor. -/
def Prepared.definition (p : Prepared) : AdventureDefinition :=
  ⟨p.proposal.ruleSet p.before,
    { p.before.hero with weapon := p.proposal.equipment.map (·.weapon) |>.getD p.before.hero.weapon },
    p.heroLegal, p.proposal.story p.before, p.storyLegal⟩

/-- Apply the definition at the original checkpoint. Wounds, enemy HP, order, and maneuvers stay. -/
def Prepared.game (p : Prepared) : Game :=
  let d := p.definition
  { rules := d.rules, hero := d.hero, heroLegal := d.heroLegal, adventure := d.story, legal := d.legal,
    hp := p.before.hp, trail := p.before.trail, policy := p.before.policy,
    phase := match p.before.phase with
      | .fight f => .fight { f with state := { f.state with hero := { f.state.hero with being := d.hero } } }
      | .scene id => if (d.story.scene? id).any (·.choices.isEmpty) then .ended id else .scene id
      | phase => phase }

/-- Every accepted preparation preserves the event graph throughout an ongoing fight. -/
theorem Prepared.fight_graph_unchanged (p : Prepared) (f : FightPhase)
    (fight : p.before.phase = .fight f) : p.game.adventure = p.before.adventure := by
  have unchanged : p.proposal.scenes = [] := by
    simpa [Proposal.graphStableInFight, fight] using p.graphStable
  simp [game, definition, Proposal.story, unchanged]

/-- State preservation does not depend on the GM following its prompt. -/
theorem Prepared.preserves_checkpoint (p : Prepared) :
    p.game.hp = p.before.hp ∧ p.game.trail = p.before.trail ∧
    p.game.sceneId? = p.before.sceneId? := by
  constructor
  · rfl
  · constructor
    · rfl
    · cases h : p.before.phase <;> try { simp [game, Game.sceneId?, h] }
      rename_i id
      by_cases empty : (p.definition.story.scene? id).any (·.choices.isEmpty) = true <;>
        simp [game, Game.sceneId?, h, empty]

/-- Installation preserves the entire paused fight except the hero's equipment-bearing identity.
In particular no wounds, maneuvers, enemy turns, or rounds are reset. -/
theorem Prepared.preserves_fight_checkpoint (p : Prepared) (f : FightPhase)
    (paused : p.before.phase = .fight f) :
    p.game.phase = .fight { f with state := { f.state with
      hero := { f.state.hero with being := p.definition.hero } } } := by
  simp [Prepared.game, paused]

/-- Every core field is unchanged, including dice, point budgets, HP rules, and turn order. -/
theorem Prepared.preserves_core (p : Prepared) :
    p.game.rules.core = p.before.rules.core := rfl

/-- A live request cannot remove or edit any existing rule, including inherited meta rules. -/
theorem Prepared.preserves_existing_rule (p : Prepared) (r : CombatRule)
    (existing : r ∈ p.before.rules.combatRules) : r ∈ p.game.rules.combatRules := by
  simp [Prepared.game, Prepared.definition, Proposal.ruleSet, existing]

/-- Sample the actual revised checkpoint at its completed-event count, without healing or rewinding. -/
def Prepared.candidate (p : Prepared) : StatisticalCandidate :=
  StatisticalCandidate.atCheckpoint p.definition p.game.balancePoint
    p.before.trail.length liveHorizon (by decide) p.before.policy

/-- A change keeps the game's balance policy, and the check uses that same policy. So the
difficulty level of an Adventure stays the same for its whole life. -/
theorem Prepared.keeps_policy (p : Prepared) :
    -- The changed game has the policy of the game before the change.
    p.game.policy = p.before.policy ∧
    -- The balance check of the change uses that policy.
    p.candidate.policy = p.before.policy := ⟨rfl, rfl⟩

/-- Both the simulator and its probability graph start from the revised checkpoint at its real age. -/
theorem Prepared.candidate_from_checkpoint (p : Prepared) :
    p.candidate.resume = some p.game.balancePoint ∧
    p.candidate.elapsed = p.before.trail.length ∧
    p.candidate.graph = continuationGraph p.definition p.game.balancePoint :=
  ⟨rfl, rfl, rfl⟩

/-- A Scene checkpoint uses the current Scene and remaining HP as its new start node. -/
theorem Prepared.candidate_scene_start (p : Prepared) (id : SceneId)
    (scene : p.before.phase = .scene id) :
    p.candidate.resume = some (.scene id p.before.hp) ∧
    p.candidate.graph.start = arrive p.definition.story id p.before.hp := by
  by_cases empty : (p.definition.story.scene? id).any (·.choices.isEmpty) = true <;>
    simp [StatisticalCandidate.atCheckpoint, candidate, game, Game.balancePoint, Game.sceneId?, scene,
      StatisticalCandidate.graph, continuationGraph, empty]

/-- Paused combat retains wounds, foes, maneuvers, order and round, with only the granted build updated. -/
theorem Prepared.candidate_fight_start (p : Prepared) (f : FightPhase)
    (fight : p.before.phase = .fight f) :
    p.before.hp = f.state.hero.hp ∧
    p.candidate.resume = some (.fight
      { f with state := { f.state with hero := { f.state.hero with being := p.definition.hero } } }) := by
  have hp := p.checkpointValid
  simp only [checkpointConsistent, fight] at hp
  exact ⟨hp, by simp [StatisticalCandidate.atCheckpoint, candidate, game, Game.balancePoint, fight]⟩

/-- Decode limits, legality and the short-loop check (`Adventure.noShortLoops`) are checked
before any simulation. `map` is the world map of the
Adventure in play, if it has one: the changed Adventure must fit the same map, with a place for each
new Scene. -/
def Proposal.prepare (p : Proposal) (g : Game) (map : Option WorldEnvironment := none) :
    Except (List String) Prepared :=
  let errs := p.errors g
  let rules := p.ruleSet g
  let hero := { g.hero with weapon := p.equipment.map (·.weapon) |>.getD g.hero.weapon }
  let story := p.story g
  let sizes := sizeErrors { adventure := story, hero, background := "", environment := p.environmentAfter map }
  if he : errs = [] then
  if hp : g.policy.Valid then
  if hk : checkpointConsistent g then
  if hs : p.graphStableInFight g then
  if sizes != [] then .error sizes else
  if hc : checkCharacter rules hero = [] then
    if ha : check rules hero story = [] then
      if hl : story.checkShortLoops then .ok ⟨g, p, he, hp, hk, hs, checkCharacter_sound hc,
        story.checkShortLoops_sound hl, check_sound ha⟩
      else .error story.shortLoopErrors
    else .error (check rules hero story ++ story.shortLoopErrors)
  else .error (checkCharacter rules hero)
  else .error ["The event graph cannot change during a fight. Finish the fight before editing scenes or choices."]
  else .error ["The checkpoint HP does not match the paused Fight."]
  else .error ["The current balance policy is invalid."]
  else .error errs

/-- Evidence is bound to this updated adventure, seed, and error allowance. -/
structure Admission (p : Prepared) (seed : Nat) (delta : Rat) where
  counts : ValidationCounts
  provenance : counts = sampleCounts p.candidate seed p.candidate.games
  accepted : p.candidate.accepts counts delta
  riskValid : 0 < delta ∧ delta ≤ confidenceDelta
  combat : CertifiedAdventureCombat p.definition
  /-- A live edit must preserve an executable checkpoint, even for custom core rules. -/
  wellFormed : p.game.WellFormed
  hpBound : p.game.hp ≤ p.game.rules.maxHP p.game.hero
  /-- The paused fight is checked with its actual wounds, maneuvers, and remaining turn order. -/
  checkpoint : match p.game.phase with
    | .fight f => CertifiedContinuation p.game.rules f
    | _ => Unit

/-- The prepared definition already carries the short-loop proof; admission reuses it. -/
theorem Admission.noShortLoops {p : Prepared} {seed : Nat} {delta : Rat}
    (_a : Admission p seed delta) : p.game.adventure.NoShortLoops := p.noShortLoops

-- The fact about one admission is `WorldChange.Admission.intervals_fit`.
/-- The balance test at error allowance `delta` is sound for the changed Adventure, from its
checkpoint. This holds for every proposal: it limits how often the test accepts an unbalanced change. It
does not say that this change is balanced. -/
theorem Admission.balanced {p : Prepared} {seed : Nat} {delta : Rat} (a : Admission p seed delta) :
    BalancedAt p.candidate delta := p.candidate.balancedAt delta (Rat.le_of_lt a.riskValid.1)

/-- Every interval that authorized the change fits the aged curve at the actual checkpoint. -/
theorem Admission.intervals_fit {p : Prepared} {seed : Nat} {delta : Rat}
    (a : Admission p seed delta) (i : Fin (p.candidate.horizon+1)) :
    let obs := a.counts.observation i.val
    let iv := confidenceInterval delta obs.trials obs.deaths
    (p.candidate.bands i).target - (p.candidate.bands i).tolerance ≤ iv.lower ∧
      iv.upper ≤ (p.candidate.bands i).target + (p.candidate.bands i).tolerance :=
  p.candidate.accepted_intervals a.counts delta a.accepted i

/-- Admission requires the complete interval to fit the original curve's conditional target within its policy tolerance. -/
theorem Admission.checkpoint_intervals {p : Prepared} {seed : Nat} {delta : Rat}
    (a : Admission p seed delta) (i : Fin (p.candidate.horizon+1)) :
    let obs := a.counts.observation i.val
    let iv := confidenceInterval delta obs.trials obs.deaths
    let target := p.before.policy.checkpointTarget p.before.trail.length i.val
    target - p.before.policy.tolerance ≤ iv.lower ∧ iv.upper ≤ target + p.before.policy.tolerance := by
  simpa only [StatisticalCandidate.bands, Prepared.candidate, StatisticalCandidate.atCheckpoint, bandsFor, balanceTolerance]
    using a.intervals_fit i

/-- The checked pair probability uses the original Weibull parameters at the true elapsed time. -/
theorem Prepared.checkpoint_pair_target (p : Prepared) (offset : Nat) :
    p.before.policy.checkpointTarget p.candidate.elapsed (offset+1) =
      1 - p.before.policy.survival (p.before.trail.length + offset + 2) /
        p.before.policy.survival (p.before.trail.length + offset) :=
  p.before.policy.checkpointTarget_pair p.policyValid p.before.trail.length offset

/-- The true probabilities refer to the revised graph at the actual checkpoint, not the old start. -/
theorem Prepared.checkpoint_pair_truth (p : Prepared) (offset : Nat)
    (within : offset + 1 < p.candidate.horizon + 1) :
    p.candidate.truth ⟨offset + 1, within⟩ =
      ((continuationGraph p.definition p.game.balancePoint).deathWithinTwo offset).getD 0 := by
  simp [StatisticalCandidate.truth, StatisticalCandidate.atCheckpoint, candidate, StatisticalCandidate.graph]

/-- The requested semantic property, for every row in the finite continuation window. -/
def Prepared.CheckpointBalanced (p : Prepared) : Prop :=
  p.candidate.FitsBands

instance (p : Prepared) : Decidable p.CheckpointBalanced := by
  unfold Prepared.CheckpointBalanced
  infer_instance

/-- If the admitted intervals cover the true checkpoint probabilities, the changed graph
meets the original aged difficulty curve within its policy tolerance at every tested row. -/
theorem Admission.difficulty_preserved_if_covered {p : Prepared} {seed : Nat} {delta : Rat}
    (a : Admission p seed delta)
    (covered : ∀ i : Fin (p.candidate.horizon + 1),
      let obs := a.counts.observation i.val
      (confidenceInterval delta obs.trials obs.deaths).Contains (p.candidate.truth i)) :
    p.CheckpointBalanced :=
  p.candidate.fits_if_covered a.counts delta a.accepted covered

/-- Under the existing binomial sampling hypotheses, accepting every checkpoint interval
while the changed graph violates the policy-band property has probability at most delta.
This is a bound on false acceptance, not a claim that a finite sample gives certainty. -/
theorem Prepared.checkpoint_falseAcceptance (p : Prepared) (delta : Rat)
    (nonnegative : 0 ≤ delta)
    (law : Distribution (Fin (p.candidate.horizon + 1) → Observation))
    (valid : law.Valid) (sampling : BinomialSampling law p.candidate.truth)
    (probabilities : ∀ i, 0 ≤ p.candidate.truth i ∧ p.candidate.truth i ≤ 1) :
    expectation law (fun observations =>
      if acceptsFamily p.candidate.bands delta observations ∧ ¬ p.CheckpointBalanced
      then 1 else 0) ≤ delta := by
  exact familyFalseAcceptance_bound law p.candidate.truth p.candidate.bands delta
    valid sampling probabilities nonnegative

/-- Validate one frozen proposal with a fresh, preassigned batch; every row must pass. -/
def Prepared.admit (p : Prepared) (seed : Nat) (delta : Rat) :
    ValidationCounts × Option (Admission p seed delta) :=
  let counts := sampleCounts p.candidate seed p.candidate.games
  if hd : 0 < delta ∧ delta ≤ confidenceDelta then
    if h : p.candidate.accepts counts delta then
      match certifyAdventureCombat p.definition with
      | none => ({counts with combatRejected := true}, none)
      | some combat =>
        if hw : p.game.WellFormed then
        if hb : p.game.hp ≤ p.game.rules.maxHP p.game.hero then
          let checkpoint : Option (match p.game.phase with
              | .fight f => CertifiedContinuation p.game.rules f | _ => Unit) :=
            match p.game.phase with
            | .fight f => certifyContinuation p.game.rules f
            | .title | .scene _ | .ended _ | .dead _ => some ()
          match checkpoint with
          | none => ({counts with combatRejected := true}, none)
          | some checkpoint => (counts, some ⟨counts, rfl, h, hd, combat, hw, hb, checkpoint⟩)
        else ({counts with combatRejected := true}, none)
        else ({counts with combatRejected := true}, none)
    else (counts, none)
  else (counts, none)

/-- Gameplay changes need statistical evidence; scenery-only changes carry an identity proof. -/
inductive Permit (p : Prepared) (seed : Nat) (delta : Rat) where
  | statistical (evidence : Admission p seed delta)
  | visual (unchanged : p.proposal.visualOnly) (wellFormed : p.game.WellFormed)
      (hpBound : p.game.hp ≤ p.game.rules.maxHP p.game.hero)

/-- Both scenery-only and statistical installations preserve runtime consistency. -/
theorem Permit.wellFormed {p : Prepared} {seed : Nat} {delta : Rat}
    (permit : Permit p seed delta) : p.game.WellFormed := by
  cases permit with
  | statistical evidence => exact evidence.wellFormed
  | visual _ valid _ => exact valid

/-- Rebuilding from the revised game preserves exact render/event correspondence after any patch. -/
theorem Prepared.spatial_matches (p : Prepared) :
    (∀ source target, (source, target) ∈ p.game.spatialProjection.links ↔ Leads p.game.adventure source target) ∧
    (∀ input, input ∈ p.game.spatialProjection.inputs ↔ AllowedInput p.game input) :=
  ⟨p.game.spatial_links_exact, p.game.spatial_inputs_exact⟩

end Rpg.WorldChange
