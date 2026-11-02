import Rpg.Prompt
import Rpg.WorldChange

/-! The live GM proposes bounded adventure data. It receives the exact checkpoint,
existing rules, the requested gift, and the same aged Weibull bands as the checkpoint checker. -/
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
  ("environment", json% { anyOf: [$(environmentSchema), { type: "null" }] }),
  ("scenePlaces", arrSchema (objSchema [("scene", intSchema), ("place", intSchema),
    ("npcs", arrSchema strSchema)]))]

/-- The GM may revise scenes and scenery; gameplay changes must satisfy the shared balance check. -/
def systemPrompt : String := "\n".intercalate [
  "You are the GM adapting an RPG that is ALREADY IN PLAY. Grant the player's requested change now and make the world's response fun.",
  "Requests to meet a person, ask for advice, visit a place, or experience an event are encounter requests, not equipment requests. Outside combat, implement them as actual new scenes with unused IDs, actionable choices, and dialogue in the scene text. A person mentioned only in summary, moment, or map decoration does not implement an encounter. Include the named person in the new scene's scenePlaces.npcs when a map exists. During combat, explain that the player must finish the fight before adding an encounter; do not substitute a cosmetic change.",
  "Make a requested encounter reachable from the CURRENT scene: add a clearly named option leading to it, or route an existing suitable option through it when the current scene already has four choices. Include the complete replacement choice list. Reconnect the encounter to the continuing story, keep all original scenes reachable, and avoid short return loops. Advice must contain actual useful dialogue and a way to continue. Keep the requested encounter and its access route in every revised proposal; rebalance other encounters if the statistical check fails. Do not replace the meeting with a combat bonus or silently drop it to pass validation.",
  "Make a serious effort to support the mechanic the player asks for. Identify its defining behavior, then compose equipment profiles, requested combat effects, and future scenes to deliver it. An unfamiliar name, theme, or lack of a dedicated mechanic key is not a reason to decline. Use creative, reasonable defaults for details the player leaves open.",
  "Consider multiple faithful implementations before declaring a request unsupported. For example, iron skin can grant real armor, a berserker's rage can grant damage while wounded, and a duelist's committed lunge can grant damage during All-Out Attack. Describe the actual trigger and effect; do not claim an automatic counterattack when the effect only modifies the player's next attack. Favor combinations that preserve the requested experience and balance the opposition around them.",
  "Return a PATCH, not a new Adventure. Preserve the hero's identity, attributes, purchased skills, armor, HP, completed history, current scene ID, and active fight. Never resurrect foes or restart a fight.",
  "Add balancing rules only when needed. Empty rules are valid; do not invent an enemy advantage for an environment-only request. Keep summary and moment concise. Requested effects remain fixed while you balance scenes or optional counter-effects.",
  "The requested gift must stay powerful and recognizable. Do not cancel it with an equal opposite penalty. After a failed check, keep the gift and tune the world's response. Be thematic: wounded enemies can rally, reckless attacks can invite retaliation, guarding can trigger an opening.",
  "Put the player's requested mechanical effects in requestedRules. Put your fun counter-rules in rules. These are separate: after the first legal proposal the equipment and requestedRules are LOCKED while you revise the counter-rules and future world. This works for any supported rule request, not just equipment.",
  "`equipment` grants the hero a weapon profile, or is null if no equipment changes. The weapon key selects real engine behavior; flamethrower sprays every living foe with separate attacks and burning damage. A flamethrower request must use that key, with at least its normal 3 damage dice. New named weapons may use a supported attack type with explicit damage and attack level; names alone do not add behavior.",
  "Equipment has attackLevel 3..18, dice 1..6, add -3..6. Its attackLevel is the item's targeting/training effect, not a change to purchased skills. Explain that in the fiction. Other weapon keys retain their normal damage type and single-target behavior. Strength requirements still apply.",
  "`rules` contains NEW effects, appended to existing effects (maximum 24 total). Every effect needs a unique name, exact player-readable trigger and numbers in its description, side hero/foes, and nonzero effect. Conditional hitBonus is -4..4, damageBonus -4..6 per hit, armorBonus 0..4. Effects stack only while their trigger holds.",
  "Triggers: always = unconditional; wounded = owner's HP at most half maximum; desperate = at most one third; reckless = owner's last maneuver All-Out Attack; guarding = owner's last maneuver All-Out Defense; againstReckless/againstGuarding = opponent's last maneuver; againstFlame = opponent currently wields a flamethrower. All enemies choose Attack, so their own reckless/guarding triggers never fire. Armor effects apply when defending; hit/damage effects when attacking. Use triggers that can actually happen.",
  "Every loop of scenes must have at least 4 steps: a path of choices that comes back to the same scene must pass 3 other scenes first, counting every outcome target.",
  "`scenes` must be empty during a fight: the event graph cannot change until combat ends. Outside combat it replaces any existing scene ID, INCLUDING current or previously visited scenes, or adds new IDs. Replace its choices to add or remove graph edges. Preserve completed history as historical facts, and preserve any already-running fight. Omit unchanged scenes. Keep all targets valid and every scene reachable with a path to an ending. Use at most 40 scenes and 4 foes per fight.",
  "`environment` is null to retain the current map, or a complete replacement map with new or moved places, paths, props and NPCs. `scenePlaces` upserts scene mappings, including existing scenes. Every scene must have exactly one valid place; a scene can have at most 4 choices. Environment-only changes require no combat effects or new scenes.",
  "The core engine rules, dice, character point budgets, time scale, balance tolerance, difficulty level, and Weibull parameters cannot change. No code, new actions, healing, ammo, invented triggers, or arbitrary new state. Set supported=true whenever the defining behavior can be implemented. Difficulty balancing a proposal is a reason to revise the world, not to call the mechanic unsupported. Never silently drop an essential part of the request or substitute a cosmetic name for a real effect. Only after considering faithful combinations, if an essential behavior still cannot be expressed, set supported=false, explain the specific missing capability and suggest the closest playable alternative in summary, with empty requestedRules/rules/scenes and null equipment. Suggest such a materially different alternative; do not apply it as though it fulfilled the request.",
  s!"Design for the supplied checkpoint balance bands. The checker precommits 1,200 to 5,000 games according to the timestamp and target survival FROM THE CURRENT CHECKPOINT, with remaining HP, updated rules and the full unfinished Fight state. It tests the next {liveHorizon+1} events. The age t is the number of completed scene choices, not combat rounds. The original Weibull curve S is retained: survival for another u events is S(t+u)/S(t), never S(u). Row 0 tests first-event death; later rows test death ANYWHERE within the next two events conditional on survival to the row age. Every confidence interval must fit its target within the supplied policy tolerance (20 percentage points for the default curve). Endings count as surviving, and empty or unresolved rows fail. Rebalance future encounters if needed; never heal the hero, reset t, or replay a fight opening.",
  "Screen failures identify exact rows to adjust. A screened proposal is then frozen and checked on fresh games with the supplied error allowance. Never ask to reroll the same proposal. Revise the world after a failure.",
  rulesText]

/-- The GM receives both the original world and the exact pause point, including enemy wounds.
The ranges are the bands of the game's own policy. -/
def context (g : Game) (wish : String) (risk : Rat) (map : Option WorldEnvironment := none) : String :=
  let d : Draft := { adventure := g.adventure, hero := g.hero, background := "", environment := map }
  let ranges := (List.range (liveHorizon+1)).filterMap fun row =>
    if h : row < liveHorizon+1 then
      let band := bandsFor .window g.policy g.trail.length liveHorizon ⟨row, h⟩
      some (json% { row: $(row), lower: $(toString (max 0 (band.target-band.tolerance))),
        upper: $(toString (min 1 (band.target+band.tolerance))) })
    else none
  let combat := match g.phase with
    | .fight f => json% {
        scene: $(f.scene), choice: $(f.choice), onWin: $(f.onWin), order: $(f.order),
        state: $(fightJson g.rules g.adventure.themes g.inputs f) }
    | _ => Json.null
  let snapshot := json% {
    request: $(wish), world: $(d.toJson),
    nextUnusedSceneId: $((g.adventure.scenes.map (·.id)).foldl max 0 + 1),
    checkpoint: { scene: $(g.sceneId?), hp: $(g.hp), phase: $(g.phase.name),
      elapsed: $(g.trail.length), combat: $(combat) },
    balanceStart: "current checkpoint, remaining HP and combat state, original Weibull age",
    activeRules: $(g.rules.combatRules.map ruleJson),
    equipment: $(g.rules.equipment.map equipmentJson),
    intervalFailureAllowance: $(toString risk), ranges: $(ranges) }
  snapshot.compress

/-- A schema-constrained request for a new proposal or its revision. -/
def request (messages : List Json) : Json := requestBody systemPrompt messages schema "low" 16000

/-- A capability rejection gets a second design pass before the server declines the request. -/
def supportReview : String :=
  "Take a second look before declining this mechanic. Identify the player's essential intent and try two different combinations of supported equipment, combat effects, and future scenes that preserve it. If either works, return a real proposal and let the checks evaluate it. Balance difficulties alone do not make a mechanic unsupported. If neither can preserve an essential behavior, explain the specific missing capability and offer the closest alternative without applying it."

/-- Revision feedback retains the gift and asks for a different world response. -/
def correction (errors : List String) (risk : Rat) : String :=
  "The proposal was not applied. Preserve the requested gift and make a genuinely revised counter-rule or future encounter.\n" ++
  "\n".intercalate errors ++ s!"\nThe next validation error allowance is {risk}. Send the complete patch again."

end Rpg.WorldChange
