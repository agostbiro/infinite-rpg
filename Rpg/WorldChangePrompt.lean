import Rpg.Prompt
import Rpg.WorldChange

/-! The live GM proposes bounded adventure data. It receives the exact checkpoint,
existing rules, the requested gift, and the same start-of-adventure balance bands as the checker:
the bands of the game's own policy (its difficulty level). -/
namespace Rpg.WorldChange
open Lean Probability Probability.Confidence

/-- The JSON representation of an active combat rule. -/
def ruleJson (r : CombatRule) : Json := json% {
  name: $(r.name), description: $(r.description), side: $(r.side), trigger: $(r.trigger),
  hitBonus: $(r.hitBonus), damageBonus: $(r.damageBonus), armorBonus: $(r.armorBonus) }

/-- The JSON representation of an equipment profile, without a caller-controlled owner. -/
def equipmentJson (e : EquipmentRule) : Json := json% {
  weapon: $(e.weapon.key), name: $(e.name), attackLevel: $(e.attackLevel), dice: $(e.dice), add: $(e.add) }

/-- Both requested effects and counter-rules use the same verified rule language. -/
def combatRuleSchema : Json := objSchema [
  ("name", strSchema), ("description", strSchema), ("side", enumSchema ["hero", "foes"]),
  ("trigger", enumSchema combatTriggers), ("hitBonus", intSchema),
  ("damageBonus", intSchema), ("armorBonus", intSchema)]

/-- Only adventure-local equipment, combat effects, and future scenes can be proposed. -/
def schema : Json := objSchema [
  ("supported", json% { type: "boolean" }),
  ("summary", strSchema), ("moment", strSchema),
  ("equipment", json% { anyOf: [$(objSchema [
    ("weapon", enumSchema (Weapon.all.map Weapon.key)), ("name", strSchema),
    ("attackLevel", intSchema), ("dice", intSchema), ("add", intSchema)]), { type: "null" }] }),
  ("requestedRules", arrSchema combatRuleSchema),
  ("rules", arrSchema combatRuleSchema),
  ("scenes", arrSchema (objSchema [
    ("id", intSchema), ("title", strSchema), ("text", strSchema),
    ("choices", arrSchema (objSchema [("text", strSchema), ("outcome", outcomeSchema)]))])),
  ("scenePlaces", arrSchema (objSchema [("scene", intSchema), ("place", intSchema),
    ("npcs", arrSchema strSchema)]))]

/-- A world change includes a fun counter-rule on its first proposal, before checking balance. -/
def systemPrompt : String := "\n".intercalate [
  "You are the GM adapting an RPG that is ALREADY IN PLAY. Grant the player's requested change now and make the world's response fun.",
  "Make a serious effort to support the mechanic the player asks for. Identify its defining behavior, then compose equipment profiles, requested combat effects, and future scenes to deliver it. An unfamiliar name, theme, or lack of a dedicated mechanic key is not a reason to decline. Use creative, reasonable defaults for details the player leaves open.",
  "Consider multiple faithful implementations before declaring a request unsupported. For example, iron skin can grant real armor, a berserker's rage can grant damage while wounded, and a duelist's committed lunge can grant damage during All-Out Attack. Describe the actual trigger and effect; do not claim an automatic counterattack when the effect only modifies the player's next attack. Favor combinations that preserve the requested experience and balance the opposition around them.",
  "Return a PATCH, not a new Adventure. Preserve the hero's identity, attributes, purchased skills, armor, HP, completed history, current scene, and active fight. Never resurrect foes or restart a fight.",
  "Consider two named counter-rule ideas internally, then return only the chosen rules. Prefer one or two concise effects with a dramatic moment and tactical choice. Include them in the FIRST proposal even if the gift alone would already be balanced. Keep summary and moment to one sentence each, describing the fiction without numerical promises. The server may tune positive enemy counter-bonuses locally; it preserves their names and triggers and displays the actual final numbers. It never tunes the requested equipment or requestedRules.",
  "The requested gift must stay powerful and recognizable. Do not cancel it with an equal opposite penalty. After a failed check, keep the gift and tune the world's response. Be thematic: wounded enemies can rally, reckless attacks can invite retaliation, guarding can trigger an opening.",
  "Put the player's requested mechanical effects in requestedRules. Put your fun counter-rules in rules. These are separate: after the first legal proposal the equipment and requestedRules are LOCKED while you revise the counter-rules and future world. This works for any supported rule request, not just equipment.",
  "`equipment` grants the hero a weapon profile, or is null if no equipment changes. The weapon key selects real engine behavior; flamethrower sprays every living foe with separate attacks and burning damage. A flamethrower request must use that key, with at least its normal 3 damage dice. New named weapons may use a supported attack type with explicit damage and attack level; names alone do not add behavior.",
  "Equipment has attackLevel 3..18, dice 1..6, add -3..6. Its attackLevel is the item's targeting/training effect, not a change to purchased skills. Explain that in the fiction. Other weapon keys retain their normal damage type and single-target behavior. Strength requirements still apply.",
  "`rules` contains NEW effects, appended to existing effects (maximum 24 total). Every effect needs a unique name, exact player-readable trigger and numbers in its description, side hero/foes, and nonzero effect. Include at least one positive enemy effect. Conditional hitBonus is -4..4, damageBonus -4..6 per hit, armorBonus 0..4. Effects stack only while their trigger holds.",
  "Triggers: always = unconditional (allowed only in requestedRules, not counter-rules); wounded = owner's HP at most half maximum; desperate = at most one third; reckless = owner's last maneuver All-Out Attack; guarding = owner's last maneuver All-Out Defense; againstReckless/againstGuarding = opponent's last maneuver; againstFlame = opponent currently wields a flamethrower. All enemies choose Attack, so their own reckless/guarding triggers never fire. Armor effects apply when defending; hit/damage effects when attacking. Use triggers that can actually happen.",
  "Every loop of scenes must have at least 4 steps: a path of choices that comes back to the same scene must pass 3 other scenes first, counting every outcome target.",
  "`scenes` replaces unvisited scene IDs or adds new IDs. Default to scenes=[] for equipment and combat-rule requests. Patch scenes only when the request needs them or a balance failure requires it; omit unchanged scenes. NEVER patch a protected scene. All original scenes remain; all scenes must be reachable and have a path to an ending. You can extend an unvisited ending to create a longer, interesting continuation. Use at most 40 total scenes; keep choices and encounters small (at most 4 foes per fight).",
  "If the world has an `environment` (its world map), keep the map: you cannot add or move places, paths, or props. Give each NEW scene ID exactly one entry in `scenePlaces` ({scene, place, npcs}) with a place id from the map, and at most 4 people in npcs. A replaced scene keeps its place. A scene can have at most 4 choices. Use scenePlaces=[] when you add no scene or the world has no map.",
  "The core engine rules, dice, character point budgets, time scale, balance tolerance, difficulty level, and Weibull parameters cannot change. No code, new actions, healing, ammo, invented triggers, or arbitrary new state. Set supported=true whenever the defining behavior can be implemented. Difficulty balancing a proposal is a reason to revise the world, not to call the mechanic unsupported. Never silently drop an essential part of the request or substitute a cosmetic name for a real effect. Only after considering faithful combinations, if an essential behavior still cannot be expressed, set supported=false, explain the specific missing capability and suggest the closest playable alternative in summary, with empty requestedRules/rules/scenes and null equipment. Suggest such a materially different alternative; do not apply it as though it fulfilled the request.",
  s!"Design for the supplied balance bands from the beginning. The checker plays {difficultyGames} games including combat FROM THE ADVENTURE START, with full initial HP and ALL updated rules equipped from turn zero. It tests the first {liveHorizon+1} scene turns. The player resumes at their existing checkpoint after acceptance; do not simulate from that checkpoint or extend the adventure merely because the player is near its ending. Later zero-observation rows fail. Combat rounds do not count as scene turns.",
  "Screen failures identify exact rows to adjust. A screened proposal is then frozen and checked on fresh games with the supplied error allowance. Never ask to reroll the same proposal. Revise the world after a failure.",
  rulesText]

/-- The GM receives both the original world and the exact pause point, including enemy wounds.
The ranges are the bands of the game's own policy. -/
def context (g : Game) (wish : String) (risk : Rat) (map : Option WorldEnvironment := none) : String :=
  let d : Draft := { adventure := g.adventure, hero := g.hero, background := "", environment := map }
  let ranges := (List.range (liveHorizon+1)).filterMap fun row =>
    if h : row < liveHorizon+1 then
      let band := confidenceBandsFor g.policy liveHorizon ⟨row, h⟩
      some (json% { row: $(row), lower: $(toString (max 0 (band.target-band.tolerance))),
        upper: $(toString (min 1 (band.target+band.tolerance))) })
    else none
  let snapshot := json% {
    request: $(wish), world: $(d.toJson),
    checkpoint: { scene: $(g.sceneId?), hp: $(g.hp), phase: $(g.phase.name) },
    balanceStart: "adventure beginning, full initial HP, updated rules",
    protectedScenes: $(protectedScenes g),
    activeRules: $(g.rules.combatRules.map ruleJson),
    equipment: $(g.rules.equipment.map equipmentJson),
    intervalFailureAllowance: $(toString risk), ranges: $(ranges) }
  snapshot.compress

/-- A schema-constrained request for a new proposal or its revision. -/
def request (messages : List Json) : Json := requestBody systemPrompt messages schema "medium" 32000

/-- A capability rejection gets a second design pass before the server declines the request. -/
def supportReview : String :=
  "Take a second look before declining this mechanic. Identify the player's essential intent and try two different combinations of supported equipment, combat effects, and future scenes that preserve it. If either works, return a real proposal with its fun counter-rule and let the checks evaluate it. Balance difficulties alone do not make a mechanic unsupported. If neither can preserve an essential behavior, explain the specific missing capability and offer the closest alternative without applying it."

/-- Revision feedback retains the gift and asks for a different world response. -/
def correction (errors : List String) (risk : Rat) : String :=
  "The proposal was not applied. Preserve the requested gift and make a genuinely revised counter-rule or future encounter.\n" ++
  "\n".intercalate errors ++ s!"\nThe next validation error allowance is {risk}. Send the complete patch again."

end Rpg.WorldChange
