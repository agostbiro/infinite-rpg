import Rpg.Play
import Rpg.EngineInvariant

/-! Static legality and runtime progress are separate invariants. These proofs connect
the current phase and combat roster to the adventure held by the game. -/
namespace Rpg

@[simp] theorem Roll.run'_pure (x : α) (rng : Rng) : (pure x : Roll α).run' rng = x := rfl

def Game.FightContext (g : Game) (f : FightPhase) : Prop :=
  ∃ sc ch foes, g.adventure.scene? f.scene = some sc ∧ sc.choices[f.choice]? = some ch ∧
    ch.outcome = .fight foes f.onWin ∧
    f.state.hero.being = g.hero ∧
    f.state.foes.map (fun x => (x.being, x.maneuver)) = foes.map (fun b => (b, .attack)) ∧
    f.order = turnOrder g.rules g.hero foes ∧ 0 < f.round

def Game.WellFormed (g : Game) : Prop :=
  match g.phase with
  | .title => g.hp = g.rules.maxHP g.hero
  | .scene id => 0 < g.hp ∧ ∃ sc, g.adventure.scene? id = some sc ∧ sc.choices ≠ []
  | .ended id => 0 < g.hp ∧ ∃ sc, g.adventure.scene? id = some sc ∧ sc.choices = []
  | .fight f => g.hp = f.state.hero.hp ∧ f.state.over = false ∧ g.FightContext f
  | .dead f => g.hp = f.state.hero.hp ∧ f.state.hero.hp ≤ 0 ∧ g.FightContext f

def Game.Terminal (g : Game) : Prop :=
  match g.phase with
  | .ended _ | .dead _ => True
  | _ => False

/-- A computable presentation of the same runtime predicate, for live edits. -/
def Game.fightContextCheck (g : Game) (f : FightPhase) : Prop :=
  match g.adventure.scene? f.scene with
  | none => False
  | some sc => match sc.choices[f.choice]? with
    | none => False
    | some ch => match ch.outcome with
      | .fight foes onWin => onWin = f.onWin ∧ f.state.hero.being = g.hero ∧
        f.state.foes.map (fun x => (x.being,x.maneuver)) = foes.map (fun b => (b,.attack)) ∧
        f.order = turnOrder g.rules g.hero foes ∧ 0 < f.round
      | _ => False

instance (g : Game) (f : FightPhase) : Decidable (g.fightContextCheck f) := by
  unfold Game.fightContextCheck
  split <;> first | infer_instance | skip
  split <;> first | infer_instance | skip
  split <;> infer_instance

theorem Game.fightContextCheck_iff (g : Game) (f : FightPhase) :
    g.fightContextCheck f ↔ g.FightContext f := by
  cases hs : g.adventure.scene? f.scene with
  | none => simp [Game.fightContextCheck, Game.FightContext, hs]
  | some sc =>
    cases hc : sc.choices[f.choice]? with
    | none => simp [Game.fightContextCheck, Game.FightContext, hs, hc]
    | some ch =>
      cases ho : ch.outcome <;> simp [Game.fightContextCheck, Game.FightContext, hs, hc, ho]
      grind

instance (g : Game) (f : FightPhase) : Decidable (g.FightContext f) :=
  decidable_of_iff (g.fightContextCheck f) (g.fightContextCheck_iff f)

instance (g : Game) : Decidable g.WellFormed := by
  unfold Game.WellFormed
  cases g.phase <;> try infer_instance
  all_goals
    split
    next id =>
      cases h : g.adventure.scene? id <;> simp only [h, Option.some.injEq, Option.noConfusion_type,
        false_and, exists_false, exists_eq_left]
      all_goals infer_instance

theorem Game.new_wellFormed (d : AdventureDefinition)
    (policy : Probability.BalancePolicy := Probability.defaultPolicy) :
    (Game.new d policy).WellFormed := rfl

theorem Game.new_alive (d : AdventureDefinition)
    (policy : Probability.BalancePolicy := Probability.defaultPolicy) :
    0 < (Game.new d policy).hp := by
  have := d.heroLegal.hp_pos
  change (0 : Int) < (d.rules.maxHP d.hero : Int)
  omega

theorem scene_lookup_exists {a : Adventure} {id : SceneId} (h : SceneExists a id) :
    ∃ sc, a.scene? id = some sc := by
  unfold Adventure.scene?
  obtain ⟨sc, hs, hid⟩ := List.mem_map.mp h
  cases he : a.scenes.find? (fun x => x.id == id) with
  | some sc => exact ⟨sc,rfl⟩
  | none =>
    have hn := List.find?_eq_none.mp he sc hs
    simp [hid] at hn

theorem scene_lookup_mem {a : Adventure} {id : SceneId} {sc : Scene}
    (h : a.scene? id = some sc) : sc ∈ a.scenes := List.mem_of_find?_eq_some h

theorem Game.choice_legal (g : Game) {id k : Nat} {sc : Scene} {ch : Choice}
    (hs : g.adventure.scene? id = some sc) (hc : sc.choices[k]? = some ch) :
    LegalOutcome g.rules g.hero g.adventure ch.outcome :=
  g.legal.outcomes sc (scene_lookup_mem hs) ch (List.mem_of_getElem? hc)

theorem Game.enter_wellFormed (g : Game) (id : SceneId) (hp : 0 < g.hp)
    (hex : SceneExists g.adventure id) : (g.enter id).1.WellFormed := by
  obtain ⟨sc, hs⟩ := scene_lookup_exists hex
  simp only [Game.enter, hs]
  split
  · next he => exact ⟨hp, sc, hs, List.isEmpty_iff.mp he⟩
  · next he => exact ⟨hp, sc, hs, fun hn => he (List.isEmpty_iff.mpr hn)⟩

theorem Game.wellFormed_progress (g : Game) (h : g.WellFormed) (hn : ¬ g.Terminal) :
    g.inputs ≠ [] := by
  cases hp : g.phase with
  | title => simp [Game.inputs, hp]
  | scene id =>
    obtain ⟨_, sc, hs, hc⟩ := (show 0 < g.hp ∧ ∃ sc, g.adventure.scene? id = some sc ∧ sc.choices ≠ [] by
      simpa [Game.WellFormed, hp] using h)
    simp [Game.inputs, hp, hs, hc]
  | fight f =>
    have ho : f.state.over = false := (show g.hp = f.state.hero.hp ∧ f.state.over = false ∧ g.FightContext f by
      simpa [Game.WellFormed, hp] using h).2.1
    simp [Game.inputs, hp, ho, fightInputs, maneuverMenu, Maneuver.attacks]
  | ended id => exact False.elim (hn (by simp [Game.Terminal, hp]))
  | dead f => exact False.elim (hn (by simp [Game.Terminal, hp]))

theorem Game.FightContext.destination {g : Game} {f : FightPhase} (h : g.FightContext f) :
    SceneExists g.adventure f.onWin := by
  obtain ⟨sc,ch,foes,hs,hc,ho,_⟩ := h
  have hl := g.choice_legal hs hc
  rw [ho] at hl
  exact hl.1 f.onWin (by simp [Outcome.targets])

theorem Game.FightContext.advance {g : Game} {f : FightPhase} (h : g.FightContext f)
    (s : FightState) (roster : f.state.SameRoster s) (round : Nat) (positive : 0 < round) :
    g.FightContext {f with state := s, round} := by
  obtain ⟨sc,ch,foes,hs,hc,ho,hh,hfs,horder,_⟩ := h
  exact ⟨sc,ch,foes,hs,hc,ho,roster.1.trans hh,roster.2.trans hfs,horder,positive⟩

theorem Game.settle_wellFormed (g : Game) (f : FightPhase) (h : g.FightContext f) :
    (g.settle f).1.WellFormed := by
  have dest := h.destination
  simp only [Game.settle]
  split
  · next hd => exact ⟨rfl, by simpa [Fighter.alive] using hd, h⟩
  · next ha =>
    have hp : 0 < f.state.hero.hp := by simpa [Fighter.alive] using ha
    split
    · exact Game.enter_wellFormed (({g with hp := f.state.hero.hp}).record f.scene f.choice f.onWin none) f.onWin hp dest
    · next hf =>
      have hal : f.state.hero.alive = true := by simp [Fighter.alive, hp]
      have hfalse : (f.state.foes.all fun x => !x.alive) = false := Bool.eq_false_iff.mpr hf
      exact ⟨rfl, by simp only [FightState.over, hal, hfalse]; rfl, h⟩

theorem Game.startFight_wellFormed (g : Game) (id k : Nat) (sc : Scene) (ch : Choice)
    (foes : List Being) (onWin : SceneId)
    (hs : g.adventure.scene? id = some sc) (hc : sc.choices[k]? = some ch)
    (ho : ch.outcome = .fight foes onWin) (rng : Rng) :
    ((g.startFight id k foes onWin).run' rng).1.WellFormed := by
  let initial : FightState :=
    {hero := {being := g.hero, hp := g.hp}, foes := foes.map fun b => {being := b, hp := g.rules.maxHP b}}
  have hr := foeTurns_roster (attack g.rules) initial
    (beforeCharacter (turnOrder g.rules g.hero foes)) rng
  apply Game.settle_wellFormed
  refine ⟨sc,ch,foes,hs,hc,ho,hr.1,?_,rfl,by change 0 < 1; decide⟩
  simpa [initial, List.map_map, Function.comp_def, StateT.run', StateT.run, Functor.map] using hr.2

theorem Game.characterTurn_wellFormed (g : Game) (f : FightPhase) (m : Maneuver)
    (target : Option Nat) (h : g.FightContext f) (rng : Rng) :
    ((g.characterTurn f m target).run' rng).1.WellFormed := by
  generalize hmrun : heroTurn g.rules f.state m (target.getD 0) rng = result
  obtain ⟨⟨mine, mineReports⟩, rng1⟩ := result
  generalize harun : foeTurns g.rules mine (afterCharacter f.order) rng1 = result
  obtain ⟨⟨after, afterReports⟩, rng2⟩ := result
  have hm : f.state.SameRoster mine := by
    have h := heroTurn_roster (attack g.rules) f.state m (target.getD 0) rng
    change f.state.SameRoster (heroTurn g.rules f.state m (target.getD 0) rng).1.1 at h
    simpa [hmrun] using h
  have ha : mine.SameRoster after := by
    have h := foeTurns_roster (attack g.rules) mine (afterCharacter f.order) rng1
    change mine.SameRoster (foeTurns g.rules mine (afterCharacter f.order) rng1).1.1 at h
    simpa [harun] using h
  have hr : 0 < f.round := by obtain ⟨_,_,_,_,_,_,_,_,_,hr⟩ := h; exact hr
  simp only [Game.characterTurn, StateT.run', Bind.bind, StateT.bind,
    Pure.pure, Functor.map, hmrun, harun]
  split
  · apply Game.settle_wellFormed
    exact h.advance _ (hm.trans ha) f.round hr
  · generalize hbrun : foeTurns g.rules after (beforeCharacter f.order) rng2 = result
    obtain ⟨⟨before, beforeReports⟩, rng3⟩ := result
    have hb := foeTurns_roster (attack g.rules) after (beforeCharacter f.order) rng2
    change after.SameRoster (foeTurns g.rules after (beforeCharacter f.order) rng2).1.1 at hb
    rw [hbrun] at hb
    apply Game.settle_wellFormed
    change g.FightContext {f with state := (foeTurns g.rules after (beforeCharacter f.order) rng2).1.1, round := f.round+1}
    rw [hbrun]
    exact h.advance _ ((hm.trans ha).trans hb) (f.round+1) (by omega)

theorem Game.choose_wellFormed (g : Game) (id k : Nat) (sc : Scene) (ch : Choice)
    (hs : g.adventure.scene? id = some sc) (hc : sc.choices[k]? = some ch)
    (hp : 0 < g.hp) (rng : Rng) : ((g.choose id k ch).run' rng).1.WellFormed := by
  have hl := g.choice_legal hs hc
  cases ho : ch.outcome with
  | goto n =>
    have dest := hl.1 n (by simp [ho, Outcome.targets])
    simpa only [Game.choose, ho, Roll.run'_pure] using
      Game.enter_wellFormed (g.record id k n none) n hp dest
  | roll t m yes no =>
    simp only [Game.choose, ho, StateT.run', Bind.bind, StateT.bind, Pure.pure, Functor.map]
    split
    apply Game.enter_wellFormed
    · exact hp
    · apply hl.1
      split <;> simp [ho, Outcome.targets]
  | fight foes onWin =>
    have h := g.startFight_wellFormed id k sc ch foes onWin hs hc ho rng
    simp only [Game.choose, ho, StateT.run', Bind.bind, StateT.bind, Pure.pure, Functor.map]
    split
    next result nextRng he =>
      change (g.startFight id k foes onWin rng).1.1.WellFormed at h
      change result.1.WellFormed
      simpa only [he] using h


theorem Game.apply_wellFormed (g : Game) (i : Input) (rng : Rng) (h : g.WellFormed) :
    ((g.apply i).run' rng).1.WellFormed := by
  cases hp : g.phase <;> cases i <;> try { simpa only [Game.apply, hp, Roll.run'_pure] using h }
  case title.begin =>
    have ht : g.hp = g.rules.maxHP g.hero := by simpa [Game.WellFormed, hp] using h
    have positive := g.heroLegal.hp_pos
    simpa only [Game.apply, hp, Roll.run'_pure] using
      g.enter_wellFormed g.adventure.start (by omega) g.legal.start_exists
  case scene.choose id k =>
    obtain ⟨positive, sc, hs, _⟩ := (show 0 < g.hp ∧ ∃ sc, g.adventure.scene? id = some sc ∧ sc.choices ≠ [] by
      simpa [Game.WellFormed, hp] using h)
    cases hc : sc.choices[k]? with
    | none => simpa only [Game.apply, hp, hs, hc, Option.bind_some, Roll.run'_pure] using h
    | some ch =>
      simpa [Game.apply, hp, hs, hc] using g.choose_wellFormed id k sc ch hs hc positive rng
  case fight.maneuver f m target =>
    have ctx : g.FightContext f := (show g.hp = f.state.hero.hp ∧ f.state.over = false ∧ g.FightContext f by
      simpa [Game.WellFormed, hp] using h).2.2
    simpa only [Game.apply, hp] using g.characterTurn_wellFormed f m target ctx rng

/-- Every external input preserves runtime consistency, including rejected inputs. -/
theorem step_wellFormed (g : Game) (i : Input) (rng : Rng) (h : g.WellFormed) :
    ((step g i).run' rng).1.WellFormed := by
  unfold step
  split
  · exact g.apply_wellFormed i rng h
  · exact h

/-- A well-formed nonterminal game always offers a rule-allowed input. -/
theorem wellFormed_has_allowed_input (g : Game) (h : g.WellFormed) (hn : ¬ g.Terminal) :
    ∃ i, AllowedInput g i := by
  cases hi : g.inputs with
  | nil => exact False.elim (g.wellFormed_progress h hn hi)
  | cons i rest => exact ⟨i, mem_inputs_iff.mp (by simp [hi])⟩

end Rpg
