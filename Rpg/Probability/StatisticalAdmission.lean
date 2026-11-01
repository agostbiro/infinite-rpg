import Rpg.Probability.Confidence
import Rpg.Probability.Simulation

/-!
Finite confidence intervals compare the adventure's conditional death expectations
with the shared Weibull targets. The theorem `fair` proves interval coverage and
bounds false acceptance under the explicitly assumed binomial sampling model.
-/
namespace Rpg.Probability
open Confidence

/-- An adventure and the fixed finite window chosen before validation. -/
structure StatisticalCandidate extends AdventureDefinition where
  horizon : Nat
  horizonPositive : 0 < horizon

/-- The fixed, independently chosen validation seed. Never search seeds for a favorable result. -/
def validationSeed : Nat := 20261103

/-- A precommitted batch size, not a number of qualifying observations per row. -/
def validationGames : Nat := 1000

/-- Combat timeouts abort validation rather than selecting only completed fights. -/
def validationRoundLimit : Nat := 200

/-- Counts from the same fixed game batch; later rows can have fewer qualifying games. -/
structure ValidationCounts where
  trials : Array Nat
  deaths : Array Nat
  games : Nat := 0
  aborted : Bool := false
  deriving Repr

/-- Add one qualifying Bernoulli observation to its row. -/
def ValidationCounts.observe (c : ValidationCounts) (row : Nat) (death : Bool) : ValidationCounts :=
  { c with
    trials := c.trials.modify row (· + 1)
    deaths := c.deaths.modify row (· + if death then 1 else 0) }

/-- All tested outcomes are known; later unresolved outcomes are outside the window. -/
def observationsComplete (horizon : Nat) (trace : Simulation.Trace) : Bool :=
  trace.finish != .invalid && (trace.finish != .censored || horizon + 1 < trace.turn)

/-- Run a fixed batch for first-turn death and conditional deaths at t+2, for t < horizon.
An unresolved outcome inside that window aborts validation. -/
def validateCounts (a : StatisticalCandidate) : ValidationCounts := Id.run do
  let h := a.horizon
  let mut counts : ValidationCounts := ⟨Array.replicate (h+1) 0, Array.replicate (h+1) 0, 0, false⟩
  let mut rng : Rng := ⟨validationSeed.toUInt64⟩
  for _ in [:validationGames] do
    let (trace, next) := (Simulation.trajectory a.toAdventureDefinition validationRoundLimit (h+1)
      a.story.start (a.rules.maxHP a.hero) 0).run rng
    rng := next
    counts := { counts with games := counts.games + 1 }
    if !observationsComplete h trace then
      return { counts with aborted := true }
    counts := counts.observe 0 (trace.finish == .dead && trace.turn == 1)
    for t in [:h] do
      if t < trace.turn then
        counts := counts.observe (t+1) (trace.finish == .dead && trace.turn == t+2)
  return counts

/-- Row zero is first-turn death; subsequent rows are conditional two-turn deaths. -/
def confidenceBands (horizon : Nat) (i : Fin (horizon+1)) : Band :=
  ⟨if i.val = 0 then 1 - defaultPolicy.survival 1 else defaultPolicy.deathAtTwo (i.val-1),
   defaultPolicy.tolerance⟩

/-- A row's actual denominator and observed death count. -/
def ValidationCounts.observation (c : ValidationCounts) (row : Nat) : Observation :=
  ⟨c.trials[row]!, c.deaths[row]!⟩

/-- Every interval from the complete fixed batch must fit its Weibull tolerance band. -/
def ValidationAccepted (horizon : Nat) (c : ValidationCounts) : Prop :=
  c.aborted = false ∧ c.games = validationGames ∧
  c.trials.size = horizon+1 ∧ c.deaths.size = horizon+1 ∧
  ∀ i : Fin (horizon+1), c.trials[i.val]! ≤ c.games ∧
    acceptsCount (confidenceBands horizon i) confidenceDelta (c.observation i.val)

instance (horizon : Nat) (c : ValidationCounts) : Decidable (ValidationAccepted horizon c) := by
  unfold ValidationAccepted
  infer_instance

/-- The true tested probabilities come from this candidate's own graph, not caller-supplied odds.
Zero-probability conditioning uses zero; the batch has no observations for such a row and will not admit it. -/
def StatisticalCandidate.truth (a : StatisticalCandidate) (i : Fin (a.horizon+1)) : Rat :=
  if i.val = 0 then a.toAdventureDefinition.graph.deadBy 1
  else (a.toAdventureDefinition.graph.deathAtTwo (i.val-1)).getD 0

/-- Finite statistical fairness under the accepted sampling model.
Each interval covers its true expectation with risk at most delta, and accepting all
Weibull comparisons when any tested comparison is false also has risk at most delta. -/
def Fair (a : StatisticalCandidate) : Prop :=
  ∀ (law : Distribution (Fin (a.horizon+1) → Observation)),
    law.Valid →
    BinomialSampling law a.truth →
    (∀ i, 0 ≤ a.truth i ∧ a.truth i ≤ 1) →
    -- Coverage holds separately for each tested conditional expectation.
    (∀ i, intervalMissProbability law a.truth confidenceDelta i ≤ confidenceDelta) ∧
    -- Accepting the entire finite window has false-acceptance risk at most delta.
    familyFalseAcceptance law a.truth (confidenceBands a.horizon)
      confidenceDelta ≤ confidenceDelta

/-- The main fairness theorem: finite confidence intervals and Weibull-band admission are sound.
Only the stated sampling-model hypotheses are required; there are no graph or tail premises. -/
theorem StatisticalCandidate.fair (a : StatisticalCandidate) : Fair a := by
  intro law valid sampling probabilities
  constructor
  -- Each interval approximates its graph-derived death-indicator expectation.
  · intro i
    exact rowConfidence law a.truth confidenceDelta i sampling
      (probabilities i).1 (probabilities i).2 (Rat.le_of_lt confidenceLevel_valid.1)
  -- Every row must pass; a violated row bounds false acceptance of the entire decision.
  · exact familyFalseAcceptance_bound law a.truth (confidenceBands a.horizon)
      confidenceDelta valid sampling probabilities (Rat.le_of_lt confidenceLevel_valid.1)

/-- An admitted adventure carries the finite fairness theorem and source-bound passing observations. -/
structure StatisticalAdventure where
  candidate : StatisticalCandidate
  fair : Fair candidate
  counts : ValidationCounts
  provenance : counts = validateCounts candidate
  accepted : ValidationAccepted candidate.horizon counts

/-- Every admitted interval fits its shared Weibull tolerance band. -/
theorem StatisticalAdventure.intervals_fit (a : StatisticalAdventure) (i : Fin (a.candidate.horizon+1)) :
    let count := a.counts.observation i.val
    let interval := confidenceInterval confidenceDelta count.trials count.deaths
    -- The entire interval is above the band's lower bound.
    (confidenceBands a.candidate.horizon i).target - (confidenceBands a.candidate.horizon i).tolerance ≤
      interval.lower ∧
    -- The entire interval is below the band's upper bound.
    interval.upper ≤
      (confidenceBands a.candidate.horizon i).target + (confidenceBands a.candidate.horizon i).tolerance :=
  (a.accepted.2.2.2.2 i).2.2.2

/-- Audit current inputs and admit only a completed, passing result. No data is pre-authorized. -/
def admitStatistically (candidate : StatisticalCandidate) :
    ValidationCounts × Option StatisticalAdventure :=
  let counts := validateCounts candidate
  if h : ValidationAccepted candidate.horizon counts then
    (counts, some ⟨candidate, candidate.fair, counts, rfl, h⟩)
  else (counts, none)

end Rpg.Probability
