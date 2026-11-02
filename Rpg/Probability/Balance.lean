import Rpg.Probability.Graph
import Rpg.Probability.Weibull
import Rpg.Check

/-!
Expectations are defined by all finite partial sums, not by an arbitrary cutoff.
An extended expectation is represented by its rational upper bounds; an infinite
expectation has no such bound. Finite confidence admission is defined in `StatisticalAdmission.lean`.
The graph uses uniform choices, including combat targets.
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

/-- Death within the next two events given survival, including successful endings among survivors. -/
def Graph.deathWithinTwo (g : Graph) (t : Nat) : Option Rat :=
  let p := 1 - g.deadBy t
  if p = 0 then none else some ((g.deadBy (t + 2) - g.deadBy t) / p)

/-- Absolute error is at most the policy tolerance, using exact rationals. -/
def WithinTolerance (actual target tolerance : Rat) : Prop :=
  target - tolerance ≤ actual ∧ actual ≤ target + tolerance

instance (actual target tolerance : Rat) : Decidable (WithinTolerance actual target tolerance) := by
  unfold WithinTolerance
  infer_instance

/-- A concrete failure found by the finite balance diagnostic. -/
inductive BalanceViolation where
  | invalidPolicy
  | notInitiallyActive
  | firstTurn (actual target : Rat)
  | atTwo (turn : Nat) (actual target : Rat)
  deriving Repr, DecidableEq

/-- An exact check for small graphs: the policy, the start state, and the death chance of each row.
It is a test tool. Admission before play uses the `validationGames`-game check instead. -/
def checkBalanceThrough (policy : BalancePolicy) (g : Graph) (horizon : Nat) : List BalanceViolation :=
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

/-- The graph always uses this definition's rules, character, and story. -/
def _root_.Rpg.AdventureDefinition.graph (a : AdventureDefinition) : Graph :=
  adventureGraph a.rules a.hero a.story

end Rpg.Probability
