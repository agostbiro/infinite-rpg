"""Emit kernel-checkable Lean certificates. Narrative text never becomes code."""
from fractions import Fraction as Q
from engine import fraction, encode


def rat(q):
    q = Q(q)
    return f"({q.numerator}/{q.denominator} : ℚ)"


def lst(xs):
    return "[" + ", ".join(xs) + "]"


def qlist(xs):
    return lst(rat(x) for x in xs)


def blist(xs):
    return lst("true" if x else "false" for x in xs)


def graph(name, data, raw=None):
    n = len(data["rows"])
    raw = raw or [list(row.items()) for row in data["rows"]]
    rows = lst(lst(f"({v}, {rat(p)})" for v,p in row) for row in raw)
    return f"""
def {name}RowsData : List (List (Nat × ℚ)) := {rows}
def {name}Rows (s : Fin {n}) : List (Fin {n} × ℚ) :=
  (({name}RowsData.getD s.val []).map fun e => (⟨e.1 % {n}, Nat.mod_lt _ (by decide)⟩, e.2))
def {name}Terminal (s : Fin {n}) : Bool := ({blist(data['terminal'])}).getD s.val false
def {name}Lose (s : Fin {n}) : Bool := ({blist(data['lose'])}).getD s.val false
def {name} : Graph {n} where
  initial := ⟨0, by decide⟩
  rows := {name}Rows
  terminal := {name}Terminal
  lose := {name}Lose
  nonneg := by
    have h : ∀ s, ({name}Rows s).all (fun e => decide (0 ≤ e.2)) = true := by decide
    intro s e he
    exact of_decide_eq_true ((List.all_eq_true.mp (h s)) e he)
  normalized := by decide
  loss_terminal := by decide
  absorbing := by decide
def {name}Paths : Paths {name} where
  rank s := ({lst(str(x) for x in data['rank'])}).getD s.val 0
  next s := ⟨(({lst(str(x) for x in data['next'])}).getD s.val 0) % {n}, Nat.mod_lt _ (by decide)⟩
  progresses := by decide
theorem {name}_terminates (s : Fin {n}) : ({name}.chain {name}.terminal).hInf s = 1 :=
  {name}Paths.terminates {name} s
"""


def horizon(name, data):
    n, N = len(data["rows"]), len(data["table"]) - 1
    values = lst(qlist(row) for row in data["table"])
    return f"""
def {name}TableData : List (List ℚ) := {values}
def {name}Horizon : Horizon {name} {name}.terminal {N} where
  table k s := ({name}TableData.getD k.val []).getD s.val 0
  zero := by decide
  step := by decide
theorem {name}_last : {name}Horizon.table ⟨{N}, by decide⟩ {name}.initial = 1 := by decide
"""


def export(document, world, reference, combat, previous=None):
    horizon_size = len(world["table"]) - 1
    timestamp = document.get("timestamp", 0)
    current = document.get("first_state", 0)
    assert len(reference["table"]) - 1 == timestamp + horizon_size
    out = [f"""import MarkovRPGLiveRules
import MarkovRPGScenes

-- Model SHA256: {document['model_hash']}
-- All numeric inputs are exact rationals; no AI-generated Lean is executed.
-- Profile: uniform Attack/Defend, ST10, HT10, static equipment; no timed item effects.
set_option maxRecDepth 100000
set_option synthInstance.maxSize 20000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
open MarkovRPG MarkovRPG.Workshop
namespace WorkshopCertificate
"""]
    out.append(graph("duel", combat, combat["raw_rows"]))
    out.append(f"""
theorem combat_mechanics : ∀ s : Fin 64, duel.rows s = equippedDuelRows {combat.get('hero_level',12)} {combat['level']} .{combat.get('hero_weapon','punch')} .{combat.get('enemy_weapon','punch')} s := by decide
theorem combat_outputs : ∀ s : Fin 64,
    duel.terminal s = duelTerminal s ∧ duel.lose s = duelLose s := by decide
def outputGoal (k : Fin 4) (s : Fin 64) : Bool := duelTerminal s && duelOutput s == k.val
def exitData : List (List ℚ) := {lst(qlist(row) for row in combat['exits'])}
def exits (k : Fin 4) : Solution duel (outputGoal k) where
  value s := (exitData.getD s.val []).getD k.val 0
  goal_terminal := by
    have h : ∀ k : Fin 4, ∀ s : Fin 64, outputGoal k s = true → duel.terminal s = true := by decide
    exact h k
  boundary := by
    have h : ∀ k : Fin 4, ∀ s : Fin 64, duel.terminal s = true →
      (exitData.getD s.val []).getD k.val 0 = if outputGoal k s then 1 else 0 := by decide
    exact h k
  harmonic := by
    have h : ∀ k : Fin 4, ∀ s : Fin 64, duel.terminal s = false →
      dot (duel.rows s) (fun v => (exitData.getD v.val []).getD k.val 0) =
        (exitData.getD s.val []).getD k.val 0 := by decide
    exact h k
theorem exit_exact (k : Fin 4) (s : Fin 64) :
    (duel.chain (outputGoal k)).hInf s = ((exits k).value s : ℝ) :=
  (exits k).exact duel duelPaths (outputGoal k) s
""")
    out.append(graph("world", world))
    n, count = len(world["nodes"]), document["character_count"]
    memberships = lst(lst(str(c) for c in node["characters"]) for node in world["nodes"])
    out.append(f"""
-- Counts refer to the actual state graph, including HP variants and outputs.
theorem generation_size : Fintype.card (Fin {n}) ≤ {document['max_nodes']} ∧
    Fintype.card (Fin {count}) = {count} := by decide
def nodeCharacters (s : Fin {n}) : List Nat := ({memberships}).getD s.val []
theorem character_coverage :
    (∀ s : Fin {n}, (nodeCharacters s).all (fun c => decide (c < {count})) = true) ∧
    (∀ c : Fin {count}, ∃ s : Fin {n}, c.val ∈ nodeCharacters s) := by decide
""")
    out.append(graph("reference", reference))
    out.append(f"""
def worldLoss : Solution world world.lose where
  value s := ({qlist(world['losses'])}).getD s.val 0
  goal_terminal := world.loss_terminal
  boundary := by decide
  harmonic := by decide
theorem loss_exact (s : Fin {n}) : (world.chain world.lose).hInf s =
    (worldLoss.value s : ℝ) :=
  worldLoss.exact world worldPaths world.lose s
""")
    # Every macro edge is linked to an exact proved terminal law, at actual entry HP.
    n = len(world["nodes"])
    for node in world["nodes"]:
        if "combat" not in node:
            continue
        s, entry = node["id"], node["combat"]["entry"]
        row = world["rows"][s]
        destinations = []
        for hp in range(4):
            destination = next((v for v in row if world["nodes"][v]["hp"] == hp), 0)
            destinations.append(destination)
        out.append(f"""
def destination{s} (k : Fin 4) : Fin {n} :=
  ⟨(({lst(str(v) for v in destinations)}).getD k.val 0) % {n}, Nat.mod_lt _ (by decide)⟩
theorem collapsed_combat_{s} (v : Fin {n}) :
    (world.chain world.lose).transition ⟨{s}, by decide⟩ v =
      ∑ k : Fin 4, if destination{s} k = v then
        (duel.chain (outputGoal k)).hInf ⟨{entry}, by decide⟩ else 0 := by
  simp_rw [exit_exact]
  rw [Graph.transition]
  have h : ∀ v : Fin {n}, weight (world.rows ⟨{s}, by decide⟩) v =
      ∑ k : Fin 4, if destination{s} k = v then (exits k).value ⟨{entry}, by decide⟩ else 0 := by decide
  simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using
    congrArg (fun q : ℚ => (q : ℝ)) (h v)
""")
    for node in world['nodes']:
        if 'combat' not in node: continue
        c=node['combat']; entry=c['entry']; baseline=rat(c.get('reference_lose',c['lose'])); band=rat(document['epsilon'])
        out.append(f"""
theorem combat_balanced_{node['id']} :
    |(duel.chain (outputGoal 0)).hInf ⟨{entry}, by decide⟩ - ({baseline} : ℝ)| ≤ ({band} : ℝ) := by
  rw [exit_exact]
  have h : |(exits 0).value ⟨{entry}, by decide⟩ - {baseline}| ≤ {band} := by decide
  exact_mod_cast h
#print axioms combat_balanced_{node['id']}
#print axioms collapsed_combat_{node['id']}
""")
    out.append(actions_certificate(world, document))
    out.append(scenes_certificate(world, document))
    if previous is not None:
        out.append(change_certificate(document, world, combat, previous))
    out.append(horizon("world", world))
    out.append(horizon("reference", reference))
    target, eps = rat(document["target"]), rat(document["epsilon"])
    out.append(f"""
def checkedState : Fin {n} := ⟨{current}, by decide⟩
noncomputable def target : Set.Icc (0 : ℝ) 1 := ⟨({target} : ℝ), by norm_num⟩
noncomputable def tolerance : ℝ≥0 := ⟨({eps} : ℝ), by norm_num⟩
theorem bernoulli_fair :
    (world.chain world.lose).IsMarkovFairBernoulli checkedState target tolerance := by
  change (world.chain world.lose).hInf checkedState ≤ ({target} : ℝ) + ({eps} : ℝ) ∧
    ({target} : ℝ) - ({eps} : ℝ) ≤ (world.chain world.lose).hInf checkedState
  rw [loss_exact]
  have h : worldLoss.value checkedState ≤ {target} + {eps} ∧
      {target} - {eps} ≤ worldLoss.value checkedState := by decide
  exact_mod_cast h
-- The reference graph is frozen. Conditioning uses absolute event time.
theorem timestamp_fair : RuleChanges.ResumedFair (world.chain world.terminal) checkedState
    (ReferenceLaw.PhaseType.law
      ⟨reference.chain reference.terminal, referencePaths.terminates reference reference.initial⟩)
    {timestamp} tolerance := by
  exact RuleChanges.resumeCheck_sound (t := {timestamp}) world reference referencePaths checkedState
    worldHorizon referenceHorizon tolerance {eps} rfl (by decide)

#print axioms generation_size
#print axioms character_coverage
#print axioms combat_mechanics
#print axioms combat_outputs
#print axioms exit_exact
#print axioms world_terminates
#print axioms loss_exact
#print axioms bernoulli_fair
#print axioms timestamp_fair
#print axioms additional_properties
#print axioms actions_match_graph
""")
    if timestamp == 0:
        out.append(f"""
theorem initial_timestamp_fair : RuleChanges.ResumedFair (world.chain world.terminal) checkedState
    (ReferenceLaw.PhaseType.law
      ⟨reference.chain reference.terminal, referencePaths.terminates reference reference.initial⟩)
    0 tolerance := timestamp_fair
-- Compatibility corollary; no duplicate numerical calculation.
theorem phase_type_fair : (world.chain world.terminal).IsMarkovFairPhaseType checkedState
    (referenceHorizon.reference reference {horizon_size} reference_last) tolerance := by
  apply (RuleChanges.resumedFair_at_zero (world.chain world.terminal) checkedState
    (referenceHorizon.reference reference {horizon_size} reference_last).law tolerance ?_).mp
  · exact timestamp_fair
  · rw [ReferenceLaw.PhaseType.cdf_law]
    change (reference.chain reference.terminal).h 0 reference.initial = 0
    rw [MarkovChain.h_zero]
    have h : reference.terminal reference.initial = false := by decide
    simp [Graph.mem_defeat, h]
#print axioms phase_type_fair
#print axioms initial_timestamp_fair
""")
    out.append("end WorkshopCertificate")
    return "\n".join(out).replace("by decide", "by decide +kernel")


def flat_actions(world):
    return [(s,label,row) for s,opts in enumerate(world['choices']) for label,row in opts.items()]


def scenes_certificate(world, doc):
    import scenes
    n = len(world['nodes'])
    events = list(dict.fromkeys(node['scene'] for node in world['nodes']))
    locations = [s['id'] for s in doc['scenes']]
    k, e = len(locations), len(events)
    membership = {node['scene']: node['scene_id'] for node in world['nodes']}
    locs = lst('none' if membership[event] is None else f'some {locations.index(membership[event])}'
               for event in events)
    state_events = lst(str(events.index(node['scene'])) for node in world['nodes'])
    rendered = lst(f'({locations.index(edge["source"])}, {locations.index(edge["target"])})'
                   for edge in doc['scene_edges'])
    contents = lst('{ objects := ' + lst(f'⟨{i}⟩' for i in s['objects']) + '.toFinset, characters := ' +
                   lst(f'⟨{c}⟩' for c in s['characters']) + '.toFinset }' for s in doc['scenes'])
    item_ids = lst(str(i['id']) for i in doc['scene_items'])
    return f"""
-- Event identity is separate from its spatial location and its HP state variants.
def stateEvent (v : Fin {n}) : Fin {e} :=
  ⟨(({state_events} : List Nat).getD v.val 0) % {e}, Nat.mod_lt _ (by decide)⟩
def eventLocation (e : Fin {e}) : Option (Fin {k}) :=
  (({locs} : List (Option Nat)).getD e.val none).map
    (fun s => ⟨s % {k}, Nat.mod_lt _ (by decide)⟩)
def sceneLayout : Scenes.Layout (Fin {e}) (Fin {k}) := Scenes.Layout.ofLocation eventLocation
theorem scene_membership_exact : ∀ v : Fin {n},
    sceneLayout.playable (stateEvent v) ↔ world.terminal v = false := by
  change ∀ v : Fin {n}, (eventLocation (stateEvent v)).isSome = true ↔ world.terminal v = false
  decide +kernel
theorem unique_active_scene (v : Fin {n}) (h : world.terminal v = false) :
    ∃! s, sceneLayout.Active stateEvent v s :=
  sceneLayout.unique_active stateEvent v ((scene_membership_exact v).mpr h)
theorem outputs_unlocated (v : Fin {n}) (h : world.terminal v = true) :
    ∀ s, ¬ sceneLayout.Active stateEvent v s := by
  apply sceneLayout.no_active_output stateEvent v
  rw [scene_membership_exact]
  simp [h]
-- Reuse the already certified sparse support; no second support table or scan.
def gameEdgePairs : List (Fin {n} × Fin {n}) := Scenes.edgesFromRows {n} edgeTargets
theorem game_edges_exact (u v : Fin {n}) : edgeB u v = true ↔ (u,v) ∈ gameEdgePairs := by
  simp [gameEdgePairs, Scenes.mem_edgesFromRows, edgeB]
def renderedScenePairs : List (Fin {k} × Fin {k}) :=
  ({rendered} : List (Nat × Nat)).map fun e =>
    (⟨e.1 % {k}, Nat.mod_lt _ (by decide)⟩, ⟨e.2 % {k}, Nat.mod_lt _ (by decide)⟩)
def renderedSceneEdge (s t : Fin {k}) : Prop := (s,t) ∈ renderedScenePairs
-- Compare computed finite edge sets; do not enumerate all scene/state quadruples.
theorem rendered_projection : renderedScenePairs.toFinset =
    (Scenes.projectEdges (eventLocation ∘ stateEvent) gameEdgePairs).toFinset := by decide
-- Exact equality: all and only the positive action outcomes between locations.
theorem scene_graph_exact : sceneLayout.Realizes stateEvent
    (fun u v => ∃ a, actions.source a = u ∧ 0 < actions.mass a v) renderedSceneEdge := by
  intro s t
  have hr : renderedSceneEdge s t ↔
      (s,t) ∈ Scenes.projectEdges (eventLocation ∘ stateEvent) gameEdgePairs := by
    simpa only [renderedSceneEdge, List.mem_toFinset] using
      (show (s,t) ∈ renderedScenePairs.toFinset ↔
        (s,t) ∈ (Scenes.projectEdges (eventLocation ∘ stateEvent) gameEdgePairs).toFinset by
          rw [rendered_projection])
  rw [hr, Scenes.mem_projectEdges]
  unfold Scenes.Layout.Edge
  simp_rw [edge_support_exact, game_edges_exact]
  simp only [Scenes.Layout.Active, sceneLayout, Scenes.Layout.ofLocation, decide_eq_true_eq,
    Function.comp_apply]
def sceneContents (s : Fin {k}) : Scenes.Scene :=
  ({contents} : List Scenes.Scene).getD s.val {{}}
theorem scene_contents_valid : ∀ s,
    (∀ i ∈ (sceneContents s).objects, i.value ∈ ({item_ids} : List Nat)) ∧
    (∀ c ∈ (sceneContents s).characters, c.value < {doc['character_count']}) := by decide
theorem scene_actions_exact (v : Fin {n}) (s : Fin {k})
    (h : sceneLayout.Active stateEvent v s) (a : Fin {len(flat_actions(world))}) :
    sceneLayout.Enabled stateEvent actions.source v s a ↔ actions.source a = v :=
  sceneLayout.enabled_iff_current_action stateEvent actions.source h a
""" + '\n'.join('#print axioms ' + name for name in scenes.PROOF_NAMES) + '\n'


def action_data(name, world):
    actions=flat_actions(world)
    return f"""
def {name} : List (Nat × List (Nat × ℚ)) :=
  {lst(f"({s}, {lst(f'({v}, {rat(p)})' for v,p in row.items())})" for s,_,row in actions)}
"""


def actions_certificate(world, doc):
    n=len(world['nodes']);m=len(flat_actions(world));maximum=rat(doc['deterministic_max'])
    edge_data=lst(lst(str(v) for v,p in row.items() if p > 0) for row in world["rows"])
    neighbors = [set() for _ in world['nodes']]
    for u,row in enumerate(world['rows']):
        for v,p in row.items():
            if p > 0 and u != v:
                neighbors[u].add(v); neighbors[v].add(u)
    neighbor_data = lst(lst(str(v) for v in sorted(row)) for row in neighbors)
    return action_data('actionsData',world)+f"""
def actionRows (i : Fin {m}) : List (Fin {n} × ℚ) :=
  ((actionsData.getD i.val (0,[])).2.map fun e =>
    (⟨e.1 % {n}, Nat.mod_lt _ (by decide)⟩,e.2))
def actions : RationalActions {n} {m} where
  source i := ⟨(actionsData.getD i.val (0,[])).1 % {n}, Nat.mod_lt _ (by decide)⟩
  mass i v := weight (actionRows i) v
  nonneg := by decide
  normalized := by decide
-- Every displayed action is retained before taking the uniform strategy.
theorem actions_match_graph : ∀ s v,
    weight (world.rows s) v =
      ((Finset.univ.filter fun a => actions.source a = s).sum fun a => actions.mass a v) /
        ((Finset.univ.filter fun a => actions.source a = s).card : ℚ) := by decide

-- Only actual positive destinations are checked against the original rows.
def edgeTargets (s : Fin {n}) : List (Fin {n}) :=
  (({edge_data} : List (List Nat)).getD s.val []).map fun v =>
    ⟨v % {n}, Nat.mod_lt _ (by decide)⟩
def edgeB (s v : Fin {n}) : Bool := (edgeTargets s).contains v
theorem edge_targets_match : ∀ s, positiveTargets (world.rows s) = edgeTargets s := by decide

-- The statement is unchanged. Its proof reuses the verified uniform average.
theorem edge_support_exact (s v : Fin {n}) :
    (∃ i, actions.source i = s ∧ 0 < actions.mass i v) ↔ edgeB s v = true := by
  rw [actions.edge_iff_positive_average s v, ← actions_match_graph s v,
      weight_pos_iff_positiveTargets _ (world.nonneg s) v, edge_targets_match]
  simp [edgeB]

def cycleNeighbors (u : Fin {n}) : List (Fin {n}) :=
  (({neighbor_data} : List (List Nat)).getD u.val []).map fun v =>
    ⟨v % {n}, Nat.mod_lt _ (by decide)⟩

theorem additional_properties : AdventureProperties.HasAdditionalProperties
    actions.source {{s | world.terminal s = true}} actions.law {maximum} := by
  apply (actions.additional_iff world.terminal {maximum}).mpr
  unfold RationalActions.numericProperties
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [edge_support_exact]
    apply AdventureProperties.noSmallCycles_of_neighbors _ cycleNeighbors
    · unfold AdventureProperties.undirected
      dsimp only
      decide +kernel
    · decide +kernel
    · have h : ∀ a : Fin {n}, (cycleNeighbors a).all (fun b =>
          (cycleNeighbors b).all (fun c => !((cycleNeighbors c).contains a))) = true := by decide
      intro a b hb c hc
      simpa using (List.all_eq_true.mp ((List.all_eq_true.mp (h a)) b hb)) c hc
  · norm_num
  · norm_num
  · decide +kernel
"""


def change_certificate(doc, world, combat, previous):
    change=doc['change'];kind=change['kind'];d=change['details'];old=previous['world']
    oldprofile=change['old_profile'];p=doc['profile'];current=change['current'];hp=change['old_hp']
    n=len(world['nodes']);oldn=len(old['nodes']);olda=flat_actions(old);m=len(olda)
    if kind=='combat':
        patch=f"{{ statistics := [(.attribute .dx, {p['dx']})], inventory := some afterPlayer.character.inventory, equipment := some afterPlayer.character.equipment }}"
        req=f".combatChange ({patch} : RuleChanges.CharacterPatch)"
    elif kind=='adventure':
        req=f".adventureStatsChange {{ statistics := [(.attribute .iq, {p['iq']})] }}"
    else:
        action=next(i for i,(s,label,_) in enumerate(olda) if s==current and label==d['action'])
        req=f".adventureStructureChange (.insertOn ⟨{action}, by decide⟩ ⟨{d['destination']}, by decide⟩)"
    out=f"""
def beforePlayer : CharacterState := liveCharacter {hp} {oldprofile['dx']} {oldprofile['iq']} .{oldprofile['weapon']}
def afterPlayer : CharacterState := liveCharacter {hp} {p['dx']} {p['iq']} .{p['weapon']}
def stopped : RuleChanges.Session (Fin {oldn}) :=
  ⟨⟨{current}, by decide⟩, beforePlayer, {change['timestamp']}, false⟩
def requested : RuleChanges.RuleChange (Fin {oldn}) (Fin {m}) := {req}
theorem rule_admitted : RuleChanges.canChange liveRules {{}} stopped [requested] = true := by decide
-- UI values must equal the actual application of the typed character patch.
theorem player_patch_exact : RuleChanges.applyBatch [requested] stopped.player = afterPlayer := by decide

def afterSession : RuleChanges.Session (Fin {n}) :=
  ⟨⟨{current}, by decide⟩, afterPlayer, {change['timestamp']}, false⟩
theorem session_preserved : afterSession.timestamp = stopped.timestamp ∧
    afterSession.position.val = stopped.position.val ∧ afterSession.player.hp = stopped.player.hp := by decide

def nodeHP : List Nat := {lst(str(x['hp']) for x in world['nodes'])}
theorem node_states_preserved : ∀ v : Fin {oldn},
    nodeHP.getD v.val 0 = ({lst(str(x['hp']) for x in old['nodes'])}).getD v.val 0 := by decide

def playerAt (v : Fin {n}) : CharacterState :=
  liveCharacter (nodeHP.getD v.val 0) {p['dx']} {p['iq']} .{p['weapon']}
theorem actual_player_input : playerAt afterSession.position = afterSession.player := by decide

theorem combat_uses_actual_player : ∀ s, duel.rows s = equippedDuelRows
    afterPlayer.character.statistics.dx {combat['level']}
    (afterPlayer.toCombat.equipment.weaponKind afterPlayer.toCombat.inventory)
    .{combat['enemy_weapon']} s := by decide

theorem characters_well_formed : ∀ v : Fin {n}, (playerAt v).WellFormed liveRules := by decide
"""
    out+=action_data('oldActionsData',old)
    newa=flat_actions(world)
    if kind in ('combat','adventure'):
        # A statistic change retains every source/action index and vertex identity.
        out+=f"""
theorem rule_scope : {len(newa)} = {len(olda)} ∧ {n} = {oldn} ∧
    actionsData.map Prod.fst = oldActionsData.map Prod.fst := by decide
"""
        preserved=[i for i,(s,_,_) in enumerate(olda) if ('combat' not in old['nodes'][s] if kind=='combat' else old['nodes'][s]['scene']!='shrine')]
        out+=f"""
theorem unrelated_actions_preserved : ∀ i ∈ ({lst(str(i) for i in preserved)} : List Nat),
    actionsData.getD i (0,[]) = oldActionsData.getD i (0,[]) := by decide
"""
        if kind=='adventure':
            oldc=previous['duel']
            out+=f"""
theorem combat_preserved : ∀ s, duel.rows s = equippedDuelRows
    {oldc['hero_level']} {oldc['level']} .{oldc['hero_weapon']} .{oldc['enemy_weapon']} s := by decide
-- Numeric action laws visibly depend on the patched IQ, not a display-only field.
"""
            for s,node in enumerate(world['nodes']):
                if node['scene']!='shrine':continue
                idx=next(i for i,(v,label,_) in enumerate(newa) if v==s and label=='Careful recovery')
                heal=next(v for v in world['rows'][s] if world['nodes'][v]['scene']=='rest')
                direct=next(v for v in world['rows'][s] if world['nodes'][v]['scene']=='detour')
                out+=f"""
theorem iq_action_{s} : actions.mass ⟨{idx}, by decide⟩ ⟨{heal}, by decide⟩ =
    (afterPlayer.character.statistics.iq : ℚ) / 20 ∧
    actions.mass ⟨{idx+1}, by decide⟩ ⟨{heal}, by decide⟩ =
    1 - (afterPlayer.character.statistics.iq : ℚ) / 20 := by decide
"""
    else:
        idx=next(i for i,(s,label,_) in enumerate(newa) if s==current and label==d['action'])
        out+=f"""
theorem rule_scope : {n} = {oldn}+1 ∧
    actions.mass ⟨{idx}, by decide⟩ ⟨{d['fresh']}, by decide⟩ =
      {rat(old['choices'][current][d['action']][d['destination']])} ∧
    actions.mass ⟨{idx}, by decide⟩ ⟨{d['destination']}, by decide⟩ = 0 ∧
    world.rows ⟨{d['fresh']}, by decide⟩ = [(⟨{d['destination']}, by decide⟩,1)] := by decide
"""
    for name in ('rule_admitted','player_patch_exact','session_preserved','node_states_preserved','actual_player_input','combat_uses_actual_player','characters_well_formed','rule_scope'):
        out+=f'\n#print axioms {name}\n'
    return out
