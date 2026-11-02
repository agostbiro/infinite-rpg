import Rpg.Probability.Combat
import Rpg.Probability.DistributionProofs

namespace Rpg.Probability

attribute [local simp] Distribution.expect_bind

/-- Merging after each enemy turn preserves every observable of the resulting state. -/
theorem foesDistribution_correct (rules : RuleSet) (s : FightState) (actors : List Actor)
    (observe : FightState → Rat) :
    (foesDistribution rules s actors).expect observe =
      (foeTurnsWith (attackDistribution rules) s actors).expect (fun result => observe result.1) := by
  induction actors generalizing s observe with
  | nil => rfl
  | cons actor actors ih =>
    cases actor with
    | none => simpa [foesDistribution, foeTurnsWith] using ih s observe
    | some i =>
      simp only [foesDistribution, Distribution.expect_collect, Distribution.expect_bind,
        Distribution.expect_map, foeTurnsWith]
      change ((foeTurnWith (attackDistribution rules) s i).bind _).expect _ = _
      simp only [Bind.bind, Distribution.expect_bind, Distribution.expect_pure]
      congr 1
      funext result
      exact ih result.1 observe

/-- The optimized round model has exactly the expectations of the shared engine round. -/
theorem roundDistribution_correct (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (roundDistribution rules policy order s).expect observe =
      (roundWith (attackDistribution rules) policy order s).expect (fun result => observe result.1) := by
  simp only [roundDistribution, Distribution.expect_collect, Distribution.expect_bind]
  rw [foesDistribution_correct]
  simp only [roundWith, Bind.bind, Distribution.expect_bind]
  congr 1
  funext before
  split <;> simp only [Distribution.expect_bind, Distribution.expect_pure]
  · exact foesDistribution_correct rules before.1 (afterCharacter order) observe
  · congr 1
    funext choice
    simp only [Distribution.expect_map]
    congr 1
    funext after
    exact foesDistribution_correct rules after.1 (afterCharacter order) observe

theorem sumAsFaces_valid (n : Nat) : (sumAsFaces n).Valid :=
  Distribution.valid_map _ _ (dice_valid n)

theorem attackWith_valid (rules : RuleSet) (a : Actor) (att : Fighter) (b : Actor) (dfn : Fighter) :
    (attackWith rules sumAsFaces a att b dfn).Valid := by
  simp only [attackWith, rollAgainstWith, damageFacesWith, Bind.bind]
  repeat first
    | exact Distribution.valid_pure _
    | exact sumAsFaces_valid _
    | apply Distribution.valid_bind
    | split
    | intro

theorem attackDistribution_valid (rules : RuleSet) (a : Actor) (att : Fighter) (b : Actor) (dfn : Fighter) :
    (attackDistribution rules a att b dfn).Valid := by
  apply Distribution.valid_map
  apply Distribution.valid_collect
  apply Distribution.valid_map
  exact attackWith_valid rules a att b dfn

theorem heroTurn_valid (rules : RuleSet) (s : FightState) (m : Maneuver) (target : Nat) :
    (heroTurnWith (attackDistribution rules) s m target).Valid := by
  have spray (att : Fighter) (foes : List Fighter) (i : Nat) :
      (sprayWith (attackDistribution rules) att i foes).Valid := by
    induction foes generalizing i with
    | nil => exact Distribution.valid_pure _
    | cons foe foes ih =>
      simp only [sprayWith, Bind.bind]
      repeat first
        | exact Distribution.valid_pure _
        | exact attackDistribution_valid _ _ _ _ _
        | exact ih _
        | apply Distribution.valid_bind
        | split
        | intro
  simp only [heroTurnWith, Bind.bind]
  repeat first
    | exact Distribution.valid_pure _
    | exact attackDistribution_valid _ _ _ _ _
    | exact spray _ _ _
    | apply Distribution.valid_bind
    | split
    | intro

theorem foeTurn_valid (rules : RuleSet) (s : FightState) (i : Nat) :
    (foeTurnWith (attackDistribution rules) s i).Valid := by
  simp only [foeTurnWith, Bind.bind]
  repeat first
    | exact Distribution.valid_pure _
    | exact attackDistribution_valid _ _ _ _ _
    | apply Distribution.valid_bind
    | split
    | intro

theorem foeTurns_valid (rules : RuleSet) (s : FightState) (actors : List Actor) :
    (foeTurnsWith (attackDistribution rules) s actors).Valid := by
  induction actors generalizing s with
  | nil => exact Distribution.valid_pure _
  | cons a actors ih =>
    cases a with
    | none => exact ih s
    | some i =>
      simp only [foeTurnsWith, Bind.bind]
      apply Distribution.valid_bind _ _ (foeTurn_valid _ _ _)
      intro first
      apply Distribution.valid_bind _ _ (ih first.1)
      intro last
      exact Distribution.valid_pure _

theorem foesDistribution_valid (rules : RuleSet) (s : FightState) (actors : List Actor) :
    (foesDistribution rules s actors).Valid := by
  induction actors generalizing s with
  | nil => exact Distribution.valid_pure _
  | cons a actors ih =>
    apply Distribution.valid_collect
    apply Distribution.valid_bind
    · exact Distribution.valid_collect _ (Distribution.valid_map _ _ (foeTurns_valid _ _ _))
    · exact ih

theorem roundDistribution_valid (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (policyValid : ∀ s, s.over = false → (policy s).Valid) (order : List Actor) (s : FightState) :
    (roundDistribution rules policy order s).Valid := by
  unfold roundDistribution
  apply Distribution.valid_collect
  apply Distribution.valid_bind
  · apply Distribution.valid_collect
    apply Distribution.valid_bind _ _ (foesDistribution_valid _ _ _)
    intro u
    split
    · exact Distribution.valid_pure _
    · next hu =>
      apply Distribution.valid_bind _ _ (policyValid u (Bool.eq_false_iff.mpr hu))
      intro choice
      exact Distribution.valid_map _ _ (heroTurn_valid _ _ _ _)
  · intro u
    exact foesDistribution_valid _ _ _

theorem livingTargets_nonempty (s : FightState) (h : s.over = false) : livingTargets s ≠ [] := by
  have hon : s.hero.alive = true ∧ ∃ foe ∈ s.foes, foe.alive = true := by
    simpa [FightState.over] using h
  obtain ⟨_,foe,hf,ha⟩ := hon
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
  have hm : i ∈ livingTargets s := by
    simp only [livingTargets, FightState.livingFoes, List.mem_filter, List.mem_range]
    exact ⟨(List.getElem?_eq_some_iff.mp hi).1, by simp [hi, ha]⟩
  intro he
  simp [he] at hm

theorem heroPolicy_valid (s : FightState) (h : s.over = false) : (heroPolicy s).Valid := by
  unfold heroPolicy
  apply Distribution.valid_bind _ _ (uniform_valid _ (by decide))
  intro m
  split
  · apply Distribution.valid_bind _ _ (uniform_valid _ (livingTargets_nonempty s h))
    intro t
    exact Distribution.valid_pure _
  · exact Distribution.valid_pure _

theorem remainingRound_valid (rules : RuleSet) (order : List Actor) (s : FightState) :
    (remainingRoundWith (attackDistribution rules) heroPolicy order s).Valid := by
  simp only [remainingRoundWith, Bind.bind]
  split
  · exact Distribution.valid_pure _
  · next h =>
    apply Distribution.valid_bind _ _ (heroPolicy_valid s (Bool.eq_false_iff.mpr h))
    intro choice
    apply Distribution.valid_bind _ _ (heroTurn_valid _ _ _ _)
    intro mine
    apply Distribution.valid_bind _ _ (foeTurns_valid _ _ _)
    intro after
    exact Distribution.valid_pure _

end Rpg.Probability
