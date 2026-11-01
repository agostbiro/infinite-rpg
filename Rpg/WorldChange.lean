import Rpg.Live
import Rpg.Probability.Retry

/-! In-play changes are checked data, not generated executable code. An accepted
patch keeps the checkpoint, HP, history, and core rules. Admission samples the
updated adventure from its beginning before the server can install it. -/
namespace Rpg.WorldChange
open Lean Probability Probability.Confidence

/-- A GM proposal contains the requested equipment, new counter-rules, and future scenes only. -/
structure Proposal where
  summary : String
  moment : String
  equipment : Option EquipmentRule
  /-- The requested effects stay fixed while the GM balances its counter-rules. -/
  requestedRules : List CombatRule := []
  rules : List CombatRule
  scenes : List Scene
  supported : Bool := true

/-- A tuned effect's description states its actual condition and numbers. -/
def counterDescription (r : CombatRule) : String :=
  let trigger := match r.trigger with
    | "wounded" => "at half HP or less"
    | "desperate" => "at one third HP or less"
    | "reckless" => "after choosing All-Out Attack"
    | "guarding" => "after choosing All-Out Defense"
    | "againstReckless" => "against an opponent using All-Out Attack"
    | "againstGuarding" => "against an opponent using All-Out Defense"
    | "againstFlame" => "against an opponent wielding a flamethrower"
    | _ => "always"
  let effects := (if r.hitBonus = 0 then [] else [s!"{r.hitBonus} to hit"]) ++
    (if r.damageBonus = 0 then [] else [s!"{r.damageBonus} damage"]) ++
    (if r.armorBonus = 0 then [] else [s!"{r.armorBonus} extra armor"])
  s!"{if r.side == "foes" then "Enemies" else "You"} gain {String.intercalate ", " effects} {trigger}."

/-- Scale only positive enemy counter-effects; keep the named tactical trigger and all gifts. -/
def tuneCounter (quarters : Nat) (r : CombatRule) : CombatRule :=
  if r.side != "foes" then r else
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
    side := ← j.getObjValAs? String "side"
    trigger := ← j.getObjValAs? String "trigger"
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
  return {
    summary := ← j.getObjValAs? String "summary"
    moment := ← j.getObjValAs? String "moment"
    equipment := gear
    requestedRules := ← listField j "requestedRules" ruleOfJson
    rules := ← listField j "rules" ruleOfJson
    scenes := (← listField j "scenes" sceneOfJson).map fun sc => { sc with picture := none }
    supported := ← j.getObjValAs? Bool "supported" }

/-- A live change can be requested between choices or on the Character's combat turn. -/
def available (g : Game) : Bool := match g.phase with
  | .scene _ => g.hp > 0
  | .fight f => !f.state.over
  | _ => false

/-- Visited scenes and the current scene are immutable; the GM can change what lies ahead. -/
def protectedScenes (g : Game) : List SceneId :=
  g.adventure.start :: g.trail.flatMap (fun t => [t.source, t.target]) ++ g.sceneId?.toList

/-- Limits keep proposals meaningful, bounded, and inside the supported adventure language. -/
def Proposal.errors (p : Proposal) (g : Game) : List String :=
  (if p.supported then [] else ["This requested behavior is outside the supported adventure rules."]) ++
  (if available g then [] else ["A change needs a living Character in a Scene or Fight."]) ++
  (if p.summary.isEmpty || p.moment.isEmpty then ["Describe the change and its dramatic player moment."] else []) ++
  (if p.equipment.isNone && p.requestedRules.isEmpty && p.scenes.isEmpty then
    ["The proposal must implement the requested change, separately from the counter-rules."] else []) ++
  tooLong "the change summary" 800 p.summary ++ tooLong "the dramatic moment" 800 p.moment ++
  (if p.rules.isEmpty then ["Add a fun counter-rule even if the requested change already passes the balance check."] else []) ++
  (if g.rules.combatRules.length + p.requestedRules.length + p.rules.length > 24 then ["At most 24 adventure effects can be active."] else []) ++
  (if !(p.rules.any fun r => r.side == "foes" && (r.hitBonus > 0 || r.damageBonus > 0 || r.armorBonus > 0))
    then ["Give the opposition a new, visible conditional advantage; do not merely cancel the gift."] else []) ++
  (if p.rules.any (fun r => r.trigger == "always") then
    ["Counter-rules need a visible condition and player decision, not a flat penalty."] else []) ++
  (p.requestedRules ++ p.rules).flatMap (fun r =>
    (if r.name.isEmpty || r.description.isEmpty then ["Every rule needs a name and description."] else []) ++
    tooLong "a rule name" 80 r.name ++ tooLong "a rule description" 400 r.description ++
    (if !["hero", "foes"].contains r.side || !combatTriggers.contains r.trigger then
      [s!"Unsupported side or trigger for {r.name}."] else []) ++
    (if r.side == "foes" && ["reckless", "guarding"].contains r.trigger then
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
  p.scenes.filterMap (fun sc => if (protectedScenes g).contains sc.id then
    some s!"Scene {sc.id} is already known. Preserve it; change or extend future Scenes instead." else none) ++
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

/-- Install or append future scenes, retaining every untouched scene and its picture. -/
def Proposal.story (p : Proposal) (g : Game) : Adventure :=
  let scenes := g.adventure.scenes.map fun sc => (p.scenes.find? (·.id == sc.id)).getD sc
  let added := p.scenes.filter fun sc => (g.adventure.scene? sc.id).isNone
  { g.adventure with scenes := scenes ++ added }

/-- A prepared change carries the legality proofs, but cannot yet be installed. -/
structure Prepared where
  before : Game
  proposal : Proposal
  proposalValid : proposal.errors before = []
  heroLegal : LegalCharacter (proposal.ruleSet before)
    { before.hero with weapon := proposal.equipment.map (·.weapon) |>.getD before.hero.weapon }
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
    hp := p.before.hp, trail := p.before.trail,
    phase := match p.before.phase with
      | .fight f => .fight { f with state := { f.state with hero := { f.state.hero with being := d.hero } } }
      | phase => phase }

/-- State preservation does not depend on the GM following its prompt. -/
theorem Prepared.preserves_checkpoint (p : Prepared) :
    p.game.hp = p.before.hp ∧ p.game.trail = p.before.trail ∧
    p.game.sceneId? = p.before.sceneId? := by
  constructor
  · rfl
  · constructor
    · rfl
    · cases h : p.before.phase <;> simp [game, Game.sceneId?, h]

/-- Every core field is unchanged, including dice, point budgets, HP rules, and turn order. -/
theorem Prepared.preserves_core (p : Prepared) :
    p.game.rules.core = p.before.rules.core := rfl

/-- The balance check starts the updated adventure at full initial HP and turn zero.
The installed game separately retains the player's actual checkpoint. -/
def Prepared.candidate (p : Prepared) : StatisticalCandidate :=
  { toAdventureDefinition := p.definition, horizon := liveHorizon, horizonPositive := by decide }

/-- The admission graph is the entire updated adventure, regardless of the pause point. -/
theorem Prepared.candidate_from_start (p : Prepared) :
    p.candidate.resume = none ∧ p.candidate.elapsed = 0 ∧
    p.candidate.graph = p.definition.graph := by
  exact ⟨rfl, rfl, rfl⟩

/-- Decode limits and legality are checked before any simulation. -/
def Proposal.prepare (p : Proposal) (g : Game) : Except (List String) Prepared :=
  let errs := p.errors g
  let rules := p.ruleSet g
  let hero := { g.hero with weapon := p.equipment.map (·.weapon) |>.getD g.hero.weapon }
  let story := p.story g
  let sizes := sizeErrors { adventure := story, hero, background := "", palette := [] }
  if he : errs = [] then
  if sizes != [] then .error sizes else
  if hc : checkCharacter rules hero = [] then
    if ha : check rules hero story = [] then
      .ok ⟨g, p, he, checkCharacter_sound hc, check_sound ha⟩
    else .error (check rules hero story)
  else .error (checkCharacter rules hero)
  else .error errs

/-- Evidence is bound to this updated adventure, seed, and error allowance. -/
structure Admission (p : Prepared) (seed : Nat) (delta : Rat) where
  counts : ValidationCounts
  provenance : counts = sampleCounts p.candidate seed validationGames
  accepted : ValidationAccepted p.candidate.horizon counts delta p.candidate.elapsed
  riskValid : 0 < delta ∧ delta ≤ confidenceDelta

-- The fact about one admission is `WorldChange.Admission.intervals_fit`.
/-- The balance test at error allowance `delta` is sound for the changed Adventure, from its
start. This holds for every proposal: it limits how often the test accepts an unbalanced change. It
does not say that this change is balanced. -/
theorem Admission.balanced {p : Prepared} {seed : Nat} {delta : Rat} (a : Admission p seed delta) :
    BalancedAt p.candidate delta := p.candidate.balancedAt delta (Rat.le_of_lt a.riskValid.1)

/-- Every interval that authorized the change fits the adventure's Weibull band from turn zero. -/
theorem Admission.intervals_fit {p : Prepared} {seed : Nat} {delta : Rat}
    (a : Admission p seed delta) (i : Fin (p.candidate.horizon+1)) :
    let obs := a.counts.observation i.val
    let iv := confidenceInterval delta obs.trials obs.deaths
    (p.candidate.bands i).target - (p.candidate.bands i).tolerance ≤ iv.lower ∧
      iv.upper ≤ (p.candidate.bands i).target + (p.candidate.bands i).tolerance :=
  (a.accepted.2.2.2.2 i).2.2.2

/-- Validate one frozen proposal with a fresh, preassigned batch; every row must pass. -/
def Prepared.admit (p : Prepared) (seed : Nat) (delta : Rat) :
    ValidationCounts × Option (Admission p seed delta) :=
  let counts := sampleCounts p.candidate seed validationGames
  if hd : 0 < delta ∧ delta ≤ confidenceDelta then
    if h : ValidationAccepted p.candidate.horizon counts delta p.candidate.elapsed then
      (counts, some ⟨counts, rfl, h, hd⟩)
    else (counts, none)
  else (counts, none)

end Rpg.WorldChange
