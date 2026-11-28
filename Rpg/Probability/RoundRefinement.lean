import Rpg.Probability.CombatProofs

/-!
# Rounds with two attack functions that give the same injuries

A round of the Engine (`roundWith`) takes an attack function. This file shows: if two attack
functions give the same expected value for every observable of the injury, then the rounds that
use them give the same expected value for every observable of the state after the round.
Reports do not count, because no observable of the state reads them.

`DiceRefinement.lean` uses this to compare the exact model with full fair dice.
`FastCombat.lean` uses it to compare the exact model with a faster attack.
-/
namespace Rpg.Probability

/-- `A` gives the same odds as `B`, with the Reports of `B` dropped. For every observable of
the attack result, the expected value under `A` equals the expected value under `B` of the same
observable applied to the injury of `B` with no Reports. -/
def ForgetsReports (A B : AttackFn Distribution) : Prop :=
  ∀ (a : Actor) (att : Fighter) (b : Actor) (dfn : Fighter) (observe : Nat × List Report → Rat),
    (A a att b dfn).expect observe = (B a att b dfn).expect (fun result => observe (result.1, []))

/-- The expected value of an `if` is the expected value of the branch that it takes. -/
theorem Distribution.expect_ite (p : Prop) [Decidable p] (d e : Distribution α)
    (f : α → Rat) : (if p then d else e).expect f = if p then d.expect f else e.expect f := by
  split <;> rfl

attribute [local simp] Distribution.expect_ite

variable {A B : AttackFn Distribution}

/-- `ForgetsReports` as an equation that `simp` can use. -/
theorem ForgetsReports.expect_eq (h : ForgetsReports A B) (a : Actor) (att : Fighter) (b : Actor)
    (dfn : Fighter) (observe : Nat × List Report → Rat) :
    (A a att b dfn).expect observe = (B a att b dfn).expect (fun result => observe (result.1, [])) :=
  h a att b dfn observe

/-- A spray gives the same odds for the Creatures under `A` and under `B`. -/
theorem spray_forgets (h : ForgetsReports A B) (att : Fighter) (foes : List Fighter)
    (i : Nat) (observe : List Fighter → Rat) :
    (sprayWith B att i foes).expect (fun r => observe r.1) =
      (sprayWith A att i foes).expect (fun r => observe r.1) := by
  induction foes generalizing i observe with
  -- No Creature is left to hit.
  | nil => simp [sprayWith]
  -- The first Creature, then the rest.
  | cons foe foes ih =>
    simp only [sprayWith]
    split <;> simp only [Bind.bind, Distribution.expect_bind, Distribution.expect_pure]
    -- The Creature is alive and is attacked.
    · simp only [h.expect_eq]
      congr 1
      funext result
      exact ih (i+1) (fun fs => observe ({foe with hp := foe.hp - result.1} :: fs))
    -- The Creature is dead and is skipped.
    · exact ih (i+1) (fun fs => observe (foe :: fs))

/-- The Character's turn gives the same odds for the state under `A` and under `B`. -/
theorem hero_forgets (h : ForgetsReports A B) (s : FightState) (m : Maneuver) (target : Nat)
    (observe : FightState → Rat) :
    (heroTurnWith B s m target).expect (fun r => observe r.1) =
      (heroTurnWith A s m target).expect (fun r => observe r.1) := by
  have hs := spray_forgets h {s.hero with maneuver := m} s.foes 0
    (fun fs => observe {s with hero := {s.hero with maneuver := m}, foes := fs})
  cases ht : s.foes[target]? <;>
    simp [heroTurnWith, Bind.bind, Distribution.expect_bind, h.expect_eq, ht] at hs ⊢
  all_goals simp only [hs]

/-- A Creature's turn gives the same odds for the state under `A` and under `B`. -/
theorem foe_forgets (h : ForgetsReports A B) (s : FightState) (i : Nat)
    (observe : FightState → Rat) :
    (foeTurnWith B s i).expect (fun r => observe r.1) =
      (foeTurnWith A s i).expect (fun r => observe r.1) := by
  cases ht : s.foes[i]? <;>
    simp [foeTurnWith, Bind.bind, Distribution.expect_bind, h.expect_eq, ht]

/-- The turns of the Creatures in `actors` give the same odds under `A` and under `B`. -/
theorem foes_forgets (h : ForgetsReports A B) (s : FightState) (actors : List Actor)
    (observe : FightState → Rat) :
    (foeTurnsWith B s actors).expect (fun r => observe r.1) =
      (foeTurnsWith A s actors).expect (fun r => observe r.1) := by
  induction actors generalizing s observe with
  -- No turn is left.
  | nil => rfl
  -- The first actor acts, then the rest of the list.
  | cons actor actors ih =>
    cases actor with
    -- The Character is in the list. Its place is skipped.
    | none => exact ih s observe
    -- Creature `i` acts, then the rest of the list.
    | some i =>
      simp only [foeTurnsWith, Bind.bind, Distribution.expect_bind, Distribution.expect_pure]
      calc
        _ = (foeTurnWith B s i).expect
            (fun r => (foeTurnsWith A r.1 actors).expect (fun q => observe q.1)) := by
          congr 1
          funext r
          exact ih r.1 observe
        _ = _ := foe_forgets h s i
          (fun state => (foeTurnsWith A state actors).expect (fun q => observe q.1))

/-- A whole round gives the same odds for the state under `A` and under `B`. -/
theorem round_forgets (h : ForgetsReports A B) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) (observe : FightState → Rat) :
    (roundWith B policy order s).expect (fun r => observe r.1) =
      (roundWith A policy order s).expect (fun r => observe r.1) := by
  let tail (attackFn : AttackFn Distribution) (state : FightState) : Rat :=
    if state.over then (foeTurnsWith attackFn state (afterCharacter order)).expect (fun r => observe r.1)
    else (policy state).expect fun choice =>
      (heroTurnWith attackFn state choice.1 choice.2).expect fun r =>
        (foeTurnsWith attackFn r.1 (afterCharacter order)).expect (fun r => observe r.1)
  simp only [roundWith, Bind.bind, Distribution.expect_ite, Distribution.expect_bind, Distribution.expect_pure]
  change (foeTurnsWith B s (beforeCharacter order)).expect (fun r => tail B r.1) =
    (foeTurnsWith A s (beforeCharacter order)).expect (fun r => tail A r.1)
  rw [foes_forgets h s (beforeCharacter order) (tail B)]
  congr 1
  funext before
  dsimp [tail]
  split
  -- The Fight is over before the Character's turn.
  · exact foes_forgets h before.1 (afterCharacter order) observe
  -- The Character acts, then the Creatures after it.
  · congr 1
    funext choice
    rw [hero_forgets h before.1 choice.1 choice.2
      (fun state => (foeTurnsWith B state (afterCharacter order)).expect (fun r => observe r.1))]
    congr 1
    funext after
    exact foes_forgets h after.1 (afterCharacter order) observe

/-- The rest of a round paused at the Character's turn gives the same odds for the state under
`A` and under `B`. -/
theorem remaining_forgets (h : ForgetsReports A B)
    (policy : FightState → Distribution (Maneuver × Nat)) (order : List Actor) (s : FightState)
    (observe : FightState → Rat) :
    (remainingRoundWith B policy order s).expect (fun r => observe r.1) =
      (remainingRoundWith A policy order s).expect (fun r => observe r.1) := by
  simp only [remainingRoundWith, Bind.bind]
  split
  -- The Fight is already over.
  · rfl
  -- The Character acts, then the Creatures after it.
  · simp only [Distribution.expect_bind, Distribution.expect_pure]
    congr 1
    funext choice
    rw [hero_forgets h s choice.1 choice.2
      (fun state => (foeTurnsWith B state (afterCharacter order)).expect (fun r => observe r.1))]
    congr 1
    funext mine
    exact foes_forgets h mine.1 (afterCharacter order) observe

end Rpg.Probability
