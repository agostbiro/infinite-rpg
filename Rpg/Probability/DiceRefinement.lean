import Rpg.Probability.CombatProofs

/-! Refinement from independent fair d6 face lists to the compressed exact model.
Reports intentionally differ: the theorem compares all rational observables of injuries
and fight states. It makes no claim about the seeded PRNG. -/
namespace Rpg.Probability

/-- Roll independent fair d6, preserving the full ordered list of faces. -/
def independentFaces : Nat → Distribution (List Nat)
  | 0 => pure []
  | n+1 => do
    let face ← uniform [1,2,3,4,5,6]
    let rest ← independentFaces n
    pure (face :: rest)

theorem independentFaces_sum (n : Nat) (observe : Nat → Rat) :
    (independentFaces n).expect (fun faces => observe faces.sum) = (dice n).expect observe := by
  induction n generalizing observe with
  | zero => simp [independentFaces, dice]
  | succ n ih =>
    simp only [independentFaces, dice, Bind.bind, Distribution.expect_collect,
      Distribution.expect_bind, Distribution.expect_pure, List.sum_cons]
    congr 1
    funext face
    exact ih (fun total => observe (face + total))

@[local simp] private theorem expect_ite (p : Prop) [Decidable p] (d e : Distribution α) (f : α → Rat) :
    (if p then d else e).expect f = if p then d.expect f else e.expect f := by
  split <;> rfl

theorem attack_injury_refinement (rules : RuleSet) (a : Actor) (att : Fighter)
    (b : Actor) (dfn : Fighter) (observe : Nat → Rat) :
    (attackWith rules independentFaces a att b dfn).expect (fun result => observe result.1) =
      (attackDistribution rules a att b dfn).expect (fun result => observe result.1) := by
  cases h : dfn.dodge rules <;>
    simp [attackDistribution, attackWith, rollAgainstWith, damageFacesWith, Bind.bind,
      Distribution.expect_bind, sumAsFaces, h]
  all_goals simp only [← independentFaces_sum]

theorem attack_expect_full (rules : RuleSet) (a : Actor) (att : Fighter)
    (b : Actor) (dfn : Fighter) (observe : Nat × List Report → Rat) :
    (attackDistribution rules a att b dfn).expect observe =
      (attackWith rules independentFaces a att b dfn).expect (fun result => observe (result.1, [])) := by
  have h := attack_injury_refinement rules a att b dfn (fun inj => observe (inj, []))
  simpa [attackDistribution] using h.symm

abbrev fullDiceAttack (rules : RuleSet) : AttackFn Distribution := attackWith rules independentFaces

theorem spray_refinement (rules : RuleSet) (att : Fighter) (foes : List Fighter)
    (i : Nat) (observe : List Fighter → Rat) :
    (sprayWith (fullDiceAttack rules) att i foes).expect (fun r => observe r.1) =
      (sprayWith (attackDistribution rules) att i foes).expect (fun r => observe r.1) := by
  induction foes generalizing i observe with
  | nil => simp [sprayWith]
  | cons foe foes ih =>
    simp only [sprayWith]
    split <;> simp only [Bind.bind, Distribution.expect_bind, Distribution.expect_pure]
    · simp only [attack_expect_full, fullDiceAttack]
      congr 1
      funext result
      exact ih (i+1) (fun fs => observe ({foe with hp := foe.hp - result.1} :: fs))
    · exact ih (i+1) (fun fs => observe (foe :: fs))

theorem hero_refinement (rules : RuleSet) (s : FightState) (m : Maneuver) (target : Nat)
    (observe : FightState → Rat) :
    (heroTurnWith (fullDiceAttack rules) s m target).expect (fun r => observe r.1) =
      (heroTurnWith (attackDistribution rules) s m target).expect (fun r => observe r.1) := by
  have hs := spray_refinement rules {s.hero with maneuver := m} s.foes 0
    (fun fs => observe {s with hero := {s.hero with maneuver := m}, foes := fs})
  cases h : s.foes[target]? <;>
    simp [heroTurnWith, Bind.bind, Distribution.expect_bind, attack_expect_full, fullDiceAttack, h] at hs ⊢
  all_goals simp only [hs]

theorem foe_refinement (rules : RuleSet) (s : FightState) (i : Nat)
    (observe : FightState → Rat) :
    (foeTurnWith (fullDiceAttack rules) s i).expect (fun r => observe r.1) =
      (foeTurnWith (attackDistribution rules) s i).expect (fun r => observe r.1) := by
  cases h : s.foes[i]? <;>
    simp [foeTurnWith, Bind.bind, Distribution.expect_bind, attack_expect_full, fullDiceAttack, h]

theorem foes_refinement (rules : RuleSet) (s : FightState) (actors : List Actor)
    (observe : FightState → Rat) :
    (foeTurnsWith (fullDiceAttack rules) s actors).expect (fun r => observe r.1) =
      (foeTurnsWith (attackDistribution rules) s actors).expect (fun r => observe r.1) := by
  induction actors generalizing s observe with
  | nil => rfl
  | cons actor actors ih =>
    cases actor with
    | none => exact ih s observe
    | some i =>
      simp only [foeTurnsWith, Bind.bind, Distribution.expect_bind, Distribution.expect_pure]
      calc
        _ = (foeTurnWith (fullDiceAttack rules) s i).expect
            (fun r => (foeTurnsWith (attackDistribution rules) r.1 actors).expect (fun q => observe q.1)) := by
          congr 1
          funext r
          exact ih r.1 observe
        _ = _ := foe_refinement rules s i
          (fun state => (foeTurnsWith (attackDistribution rules) state actors).expect (fun q => observe q.1))

theorem round_refinement (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (roundWith (fullDiceAttack rules) policy order s).expect (fun r => observe r.1) =
      (roundWith (attackDistribution rules) policy order s).expect (fun r => observe r.1) := by
  let tail (attackFn : AttackFn Distribution) (state : FightState) : Rat :=
    if state.over then (foeTurnsWith attackFn state (afterCharacter order)).expect (fun r => observe r.1)
    else (policy state).expect fun choice =>
      (heroTurnWith attackFn state choice.1 choice.2).expect fun r =>
        (foeTurnsWith attackFn r.1 (afterCharacter order)).expect (fun r => observe r.1)
  simp only [roundWith, Bind.bind, expect_ite, Distribution.expect_bind, Distribution.expect_pure]
  change (foeTurnsWith (fullDiceAttack rules) s (beforeCharacter order)).expect (fun r => tail (fullDiceAttack rules) r.1) =
    (foeTurnsWith (attackDistribution rules) s (beforeCharacter order)).expect (fun r => tail (attackDistribution rules) r.1)
  rw [foes_refinement rules s (beforeCharacter order) (tail (fullDiceAttack rules))]
  congr 1
  funext before
  dsimp [tail]
  split
  · exact foes_refinement rules before.1 (afterCharacter order) observe
  · congr 1
    funext choice
    rw [hero_refinement rules before.1 choice.1 choice.2
      (fun state => (foeTurnsWith (fullDiceAttack rules) state (afterCharacter order)).expect (fun r => observe r.1))]
    congr 1
    funext after
    exact foes_refinement rules after.1 (afterCharacter order) observe

/-- The exact model preserves every state observable of independent full-face execution. -/
theorem roundDistribution_correct_fullDice (rules : RuleSet)
    (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (roundDistribution rules policy order s).expect observe =
      (roundWith (fullDiceAttack rules) policy order s).expect (fun r => observe r.1) :=
  (roundDistribution_correct rules policy order s observe).trans
    (round_refinement rules policy order s observe).symm

end Rpg.Probability
