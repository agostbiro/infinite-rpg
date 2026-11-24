import Rpg.Probability.RoundRefinement

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

/-- The compressed attack forgets only the Reports of the full-dice attack. -/
theorem attackDistribution_forgets (rules : RuleSet) :
    ForgetsReports (attackDistribution rules) (fullDiceAttack rules) :=
  attack_expect_full rules

theorem round_refinement (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (roundWith (fullDiceAttack rules) policy order s).expect (fun r => observe r.1) =
      (roundWith (attackDistribution rules) policy order s).expect (fun r => observe r.1) :=
  round_forgets (attackDistribution_forgets rules) policy order s observe

/-- The exact model preserves every state observable of independent full-face execution. -/
theorem roundDistribution_correct_fullDice (rules : RuleSet)
    (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (roundDistribution rules policy order s).expect observe =
      (roundWith (fullDiceAttack rules) policy order s).expect (fun r => observe r.1) :=
  (roundDistribution_correct rules policy order s observe).trans
    (round_refinement rules policy order s observe).symm

end Rpg.Probability
