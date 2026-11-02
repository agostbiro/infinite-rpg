import Rpg.Engine

namespace Rpg

/-- Combat changes wounds and the hero's maneuver, never either roster. -/
def FightState.SameRoster (s t : FightState) : Prop :=
  t.hero.being = s.hero.being ∧ t.foes.map (fun f => (f.being, f.maneuver)) = s.foes.map (fun f => (f.being, f.maneuver))

theorem FightState.SameRoster.refl (s : FightState) : s.SameRoster s := ⟨rfl,rfl⟩

theorem FightState.SameRoster.trans {s t u : FightState}
    (h : s.SameRoster t) (h' : t.SameRoster u) : s.SameRoster u :=
  ⟨h'.1.trans h.1, h'.2.trans h.2⟩

theorem hurtFoe_roster (foes : List Fighter) (i inj : Nat) :
    (hurtFoe foes i inj).map (fun f => (f.being, f.maneuver)) = foes.map (fun f => (f.being, f.maneuver)) := by
  induction foes generalizing i with
  | nil => simp [hurtFoe]
  | cons f fs ih => cases i <;> simp_all [hurtFoe, List.modify]

theorem foeTurn_roster (attackFn : AttackFn Roll) (s : FightState) (i : Nat) (rng : Rng) :
    s.SameRoster ((foeTurnWith attackFn s i).run' rng).1 := by
  simp only [foeTurnWith]
  split
  · exact .refl _
  · split
    · split
      · exact .refl _
      · exact ⟨rfl, rfl⟩
    · exact .refl _

theorem spray_roster (attackFn : AttackFn Roll) (att : Fighter) (foes : List Fighter)
    (i : Nat) (rng : Rng) :
    (((sprayWith attackFn att i foes).run' rng).1.map (fun f => (f.being, f.maneuver))) = foes.map (fun f => (f.being, f.maneuver)) := by
  induction foes generalizing i rng with
  | nil => rfl
  | cons foe foes ih =>
    simp only [sprayWith]
    split
    · change (foe.being, foe.maneuver) :: (((sprayWith attackFn att (i+1) foes).run'
        ((attackFn none att (some i) foe).run rng).2).1.map (fun f => (f.being, f.maneuver))) = _
      rw [ih]; rfl
    · change (foe.being, foe.maneuver) :: (((sprayWith attackFn att (i+1) foes).run' rng).1.map (fun f => (f.being, f.maneuver))) = _
      rw [ih]; rfl

theorem heroTurn_roster (attackFn : AttackFn Roll) (s : FightState) (m : Maneuver) (t : Nat) (rng : Rng) :
    s.SameRoster ((heroTurnWith attackFn s m t).run' rng).1 := by
  simp only [heroTurnWith]
  split
  · exact .refl _
  · split
    · exact ⟨rfl,rfl⟩
    · split
      · exact ⟨rfl, spray_roster attackFn _ _ _ rng⟩
      · split
        · split
          · exact .refl _
          · exact ⟨rfl, hurtFoe_roster _ _ _⟩
        · exact .refl _

theorem foeTurns_roster (attackFn : AttackFn Roll) (s : FightState) (actors : List Actor) (rng : Rng) :
    s.SameRoster ((foeTurnsWith attackFn s actors).run' rng).1 := by
  induction actors generalizing s rng with
  | nil => exact .refl _
  | cons a rest ih =>
    cases a with
    | none => exact ih s rng
    | some i =>
      have h := foeTurn_roster attackFn s i rng
      have ht := ih ((foeTurnWith attackFn s i).run' rng).1
        ((foeTurnWith attackFn s i).run rng).2
      exact h.trans ht

theorem heroTurn_hp (attackFn : AttackFn Roll) (s : FightState) (m : Maneuver) (t : Nat) (rng : Rng) :
    ((heroTurnWith attackFn s m t).run' rng).1.hero.hp = s.hero.hp := by
  simp only [heroTurnWith]
  repeat first | rfl | split

theorem foeTurn_hp (attackFn : AttackFn Roll) (s : FightState) (i : Nat) (rng : Rng) :
    ((foeTurnWith attackFn s i).run' rng).1.hero.hp ≤ s.hero.hp := by
  simp only [foeTurnWith]
  split
  · exact Int.le_refl _
  · split
    · split
      · exact Int.le_refl _
      · change s.hero.hp - (((attackFn (some i) _ none _).run' rng).1 : Int) ≤ s.hero.hp
        omega
    · exact Int.le_refl _

theorem foeTurns_hp (attackFn : AttackFn Roll) (s : FightState) (actors : List Actor) (rng : Rng) :
    ((foeTurnsWith attackFn s actors).run' rng).1.hero.hp ≤ s.hero.hp := by
  induction actors generalizing s rng with
  | nil => exact Int.le_refl _
  | cons a rest ih =>
    cases a with
    | none => exact ih s rng
    | some i =>
      exact Int.le_trans (ih ((foeTurnWith attackFn s i).run' rng).1
        ((foeTurnWith attackFn s i).run rng).2) (foeTurn_hp attackFn s i rng)

end Rpg
