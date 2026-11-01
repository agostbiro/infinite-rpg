import Rpg.Probability.Graph
import Rpg.Probability.Weibull
import Rpg.Check

/-!
Expectations are defined by all finite partial sums, not by an arbitrary cutoff.
An extended expectation is represented by its rational upper bounds; an infinite
expectation has no such bound. Fairness applies at every turn with positive
probability of an ongoing game, under uniform choices (including combat targets).
-/
namespace Rpg.Probability

/-- An exact nonnegative extended value, represented by its rational upper bounds. -/
structure ExtendedExpectation where
  boundedBy : Rat → Prop

/-- The supremum of a sequence, without rounding or requiring a Real library. -/
def supremumExpectation (partialValues : Nat → Rat) : ExtendedExpectation :=
  ⟨fun bound => ∀ n, partialValues n ≤ bound⟩

/-- An expectation is infinite if no rational upper bound exists. -/
def ExtendedExpectation.IsInfinite (e : ExtendedExpectation) : Prop :=
  ∀ bound, ¬ e.boundedBy bound

/-- A rational is the exact value when it has the same upper bounds. -/
def ExtendedExpectation.Equals (e : ExtendedExpectation) (value : Rat) : Prop :=
  ∀ bound, e.boundedBy bound ↔ value ≤ bound

/-- E[min(termination time, n)], counting one turn per scene choice. -/
def Graph.terminationPartial (g : Graph) (n : Nat) : Rat :=
  ((List.range n).map g.activeAt).sum

/-- E[min(death time, n)]; successful endings have infinite death time. -/
def Graph.deathPartial (g : Graph) (n : Nat) : Rat :=
  ((List.range n).map fun t => 1 - g.deadBy t).sum

/-- Expected turns until either successful ending or death, possibly infinite. -/
def Graph.expectedTimeToTermination (g : Graph) : ExtendedExpectation :=
  supremumExpectation g.terminationPartial

/-- Expected turns until death, possibly infinite even when termination is certain. -/
def Graph.expectedTimeToDeath (g : Graph) : ExtendedExpectation :=
  supremumExpectation g.deathPartial

/-- Sum of t * P(death at t) over deaths observed by the given horizon. -/
def Graph.deathMoment (g : Graph) (n : Nat) : Rat :=
  ((List.range n).map fun t =>
    ((t + 1 : Nat) : Rat) * (g.deadBy (t + 1) - g.deadBy t)).sum

/-- E[death time | death by n], undefined when death by n has probability zero. -/
def Graph.conditionalDeathPartial (g : Graph) (n : Nat) : Option Rat :=
  let p := g.deadBy n
  if p = 0 then none else some (g.deathMoment n / p)

/-- Conditional expected death time requires positive eventual death probability.
Its upper bounds are those of all finite-horizon conditional expectations. -/
def Graph.expectedTimeToDeathGivenDeath (g : Graph) : Prop × ExtendedExpectation :=
  (∃ n, 0 < g.deadBy n,
    ⟨fun bound => ∀ n value, g.conditionalDeathPartial n = some value → value ≤ bound⟩)

/-- P(death exactly at t+2 | game still running at t).
Successful endings are excluded from the conditioning event. -/
def Graph.deathAtTwo (g : Graph) (t : Nat) : Option Rat :=
  let p := g.activeAt t
  if p = 0 then none else some ((g.deadBy (t + 2) - g.deadBy (t + 1)) / p)

/-- Absolute error is at most the policy tolerance, using exact rationals. -/
def WithinTolerance (actual target tolerance : Rat) : Prop :=
  target - tolerance ≤ actual ∧ actual ≤ target + tolerance

instance (actual target tolerance : Rat) : Decidable (WithinTolerance actual target tolerance) := by
  unfold WithinTolerance
  infer_instance

/-- All reachable times must satisfy the two-turn conditional Weibull bound.
The game must start active; the first-turn bound prevents an immediate-death loophole.
Graph normalization and absorbing terminal states are also required. -/
def isFair (policy : FairnessPolicy) (g : Graph) : Prop :=
  policy.Valid ∧ g.Valid ∧
  g.activeAt 0 = 1 ∧
  WithinTolerance (g.deadBy 1) (1 - policy.survival 1) policy.tolerance ∧
  ∀ t actual, g.deathAtTwo t = some actual →
    WithinTolerance actual (policy.deathAtTwo t) policy.tolerance

/-- A fairness certificate bounds the conditional probability at any requested turn. -/
theorem isFair_bounds
    (fair : isFair policy g)
    (observed : g.deathAtTwo t = some actual) :
    WithinTolerance actual (policy.deathAtTwo t) policy.tolerance :=
  fair.2.2.2.2 t actual observed

/-- A counterexample at one turn rules out an all-time fairness certificate. -/
theorem not_isFair_of_violation
    (observed : g.deathAtTwo t = some actual)
    (violates : ¬ WithinTolerance actual (policy.deathAtTwo t) policy.tolerance) :
    ¬ isFair policy g := by
  intro fair
  exact violates (isFair_bounds fair observed)

/-- A concrete failure found by the finite fairness diagnostic. -/
inductive FairnessViolation where
  | invalidPolicy
  | notInitiallyActive
  | firstTurn (actual target : Rat)
  | atTwo (turn : Nat) (actual target : Rat)
  deriving Repr, DecidableEq

/-- Check the policy, initial state, first-turn bound, and two-turn bounds for t < horizon.
This does not prove all-time fairness or normalization of the whole graph. -/
def checkFairnessThrough (policy : FairnessPolicy) (g : Graph) (horizon : Nat) : List FairnessViolation :=
  let policyErrors := if policy.Valid then [] else [.invalidPolicy]
  let initialErrors := if g.activeAt 0 = 1 then [] else [.notInitiallyActive]
  let firstTarget := 1 - policy.survival 1
  let firstErrors := if WithinTolerance (g.deadBy 1) firstTarget policy.tolerance then []
    else [.firstTurn (g.deadBy 1) firstTarget]
  let laterErrors := (List.range horizon).filterMap fun t => match g.deathAtTwo t with
    | none => none
    | some actual => if WithinTolerance actual (policy.deathAtTwo t) policy.tolerance then none
      else some (.atTwo t actual (policy.deathAtTwo t))
  policyErrors ++ initialErrors ++ firstErrors ++ laterErrors

/-- An adventure owns its rules, character, and story, with proofs tied to those values. -/
structure AdventureDefinition where
  rules : RuleSet
  hero : Being
  heroLegal : LegalCharacter rules hero
  story : Adventure
  legal : LegalAdventure rules hero story

/-- The graph always uses this definition's rules, character, and story. -/
def AdventureDefinition.graph (a : AdventureDefinition) : Graph :=
  adventureGraph a.rules a.hero a.story

/-- A playable certified story must prove the shared policy on its derived graph. -/
structure CertifiedAdventure extends AdventureDefinition where
  fair : isFair defaultPolicy (adventureGraph rules hero story)

/-- Every certified story satisfies the global policy; authors cannot choose a weaker one. -/
theorem CertifiedAdventure.isFair (a : CertifiedAdventure) :
    isFair defaultPolicy a.toAdventureDefinition.graph :=
  a.fair

end Rpg.Probability
