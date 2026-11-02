import Rpg.RuntimeInvariant

namespace Rpg

@[simp] theorem Game.enter_hp (g : Game) (id : SceneId) : (g.enter id).1.hp = g.hp := by
  simp only [Game.enter]
  split <;> rfl

@[simp] theorem Game.settle_hp (g : Game) (f : FightPhase) : (g.settle f).1.hp = f.state.hero.hp := by
  simp only [Game.settle]
  split
  · rfl
  · split
    · exact Game.enter_hp _ _
    · rfl

theorem Game.startFight_hp (g : Game) (id k : Nat) (foes : List Being) (onWin : SceneId) (rng : Rng) :
    ((g.startFight id k foes onWin).run' rng).1.hp ≤ g.hp := by
  have h := foeTurns_hp (attack g.rules)
    {hero := {being := g.hero,hp := g.hp}, foes := foes.map fun b => {being := b,hp := g.rules.maxHP b}}
    (beforeCharacter (turnOrder g.rules g.hero foes)) rng
  simp only [Game.startFight, StateT.run', Bind.bind, StateT.bind, Functor.map, Pure.pure]
  split
  next result nextRng he =>
    change (g.settle ⟨id,k,onWin,turnOrder g.rules g.hero foes,1,result.1⟩).1.hp ≤ g.hp
    rw [Game.settle_hp]
    change (foeTurns g.rules _ _ rng).1.1.hero.hp ≤ g.hp at h
    simpa only [he] using h

theorem Game.characterTurn_hp (g : Game) (f : FightPhase) (m : Maneuver) (target : Option Nat) (rng : Rng) :
    ((g.characterTurn f m target).run' rng).1.hp ≤ f.state.hero.hp := by
  generalize hmrun : heroTurn g.rules f.state m (target.getD 0) rng = result
  obtain ⟨⟨mine, mineReports⟩, rng1⟩ := result
  generalize harun : foeTurns g.rules mine (afterCharacter f.order) rng1 = result
  obtain ⟨⟨after, afterReports⟩, rng2⟩ := result
  have hm : mine.hero.hp = f.state.hero.hp := by
    have h := heroTurn_hp (attack g.rules) f.state m (target.getD 0) rng
    change (heroTurn g.rules f.state m (target.getD 0) rng).1.1.hero.hp = _ at h
    simpa [hmrun] using h
  have ha : after.hero.hp ≤ mine.hero.hp := by
    have h := foeTurns_hp (attack g.rules) mine (afterCharacter f.order) rng1
    change (foeTurns g.rules mine (afterCharacter f.order) rng1).1.1.hero.hp ≤ _ at h
    simpa [harun] using h
  simp only [Game.characterTurn, StateT.run', Bind.bind, StateT.bind,
    Pure.pure, Functor.map, hmrun, harun]
  split
  · change (g.settle {f with state := after}).1.hp ≤ f.state.hero.hp
    rw [Game.settle_hp]
    change after.hero.hp ≤ f.state.hero.hp
    omega
  · generalize hbrun : foeTurns g.rules after (beforeCharacter f.order) rng2 = result
    obtain ⟨⟨before, beforeReports⟩, rng3⟩ := result
    have hb := foeTurns_hp (attack g.rules) after (beforeCharacter f.order) rng2
    change (foeTurns g.rules after (beforeCharacter f.order) rng2).1.1.hero.hp ≤ _ at hb
    rw [hbrun] at hb
    change (g.settle {f with state := (foeTurns g.rules after (beforeCharacter f.order) rng2).1.1, round := f.round+1}).1.hp ≤ _
    rw [hbrun, Game.settle_hp]
    change before.hero.hp ≤ f.state.hero.hp
    change before.hero.hp ≤ after.hero.hp at hb
    omega

theorem Game.choose_hp (g : Game) (id k : Nat) (ch : Choice) (rng : Rng) :
    ((g.choose id k ch).run' rng).1.hp ≤ g.hp := by
  cases ho : ch.outcome with
  | goto n =>
    simp only [Game.choose, ho, Roll.run'_pure]
    change ((g.record id k n none).enter n).1.hp ≤ g.hp
    rw [Game.enter_hp]
    exact Int.le_refl _
  | roll t m yes no =>
    simp only [Game.choose, ho, StateT.run', Bind.bind, StateT.bind, Pure.pure, Functor.map]
    split
    next result nextRng _ =>
      change ((g.record id k (if result.1.succeeded then yes else no) (some result.1.succeeded)).enter
        (if result.1.succeeded then yes else no)).1.hp ≤ g.hp
      rw [Game.enter_hp]
      exact Int.le_refl _
  | fight foes onWin =>
    have h := g.startFight_hp id k foes onWin rng
    simp only [Game.choose, ho, StateT.run', Bind.bind, StateT.bind, Pure.pure, Functor.map]
    split
    next result nextRng he =>
      change (g.startFight id k foes onWin rng).1.1.hp ≤ _ at h
      change result.1.hp ≤ g.hp
      simpa only [he] using h

/-- Together with initialization, this justifies certifying only entry HPs up to the maximum. -/
theorem Game.apply_hp (g : Game) (i : Input) (rng : Rng) (h : g.WellFormed) :
    ((g.apply i).run' rng).1.hp ≤ g.hp := by
  cases hp : g.phase <;> cases i <;>
    try { simp only [Game.apply, hp, Roll.run'_pure]; exact Int.le_refl _ }
  case title.begin => simpa only [Game.apply, hp, Roll.run'_pure, Game.enter_hp] using Int.le_refl g.hp
  case scene.choose id k =>
    simp only [Game.apply, hp]
    split
    · exact g.choose_hp _ _ _ rng
    · exact Int.le_refl _
  case fight.maneuver f m target =>
    have same : g.hp = f.state.hero.hp := by
      have h' : g.hp = f.state.hero.hp ∧ f.state.over = false ∧ g.FightContext f := by
        simpa [Game.WellFormed, hp] using h
      exact h'.1
    simpa only [Game.apply, hp, same] using g.characterTurn_hp f m target rng

theorem step_hp_nonincreasing (g : Game) (i : Input) (rng : Rng) (h : g.WellFormed) :
    ((step g i).run' rng).1.hp ≤ g.hp := by
  unfold step
  split
  · exact g.apply_hp i rng h
  · exact Int.le_refl _

end Rpg
