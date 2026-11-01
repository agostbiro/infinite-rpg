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
  policy : FairnessPolicy := defaultPolicy

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

/-- Collect a fixed batch for first-turn death and conditional deaths at t+2.
Exploration can use a separate seed; unresolved outcomes inside the window abort the batch. -/
def sampleCounts (a : StatisticalCandidate) (seed games : Nat) : ValidationCounts := Id.run do
  let h := a.horizon
  let mut counts : ValidationCounts := ⟨Array.replicate (h+1) 0, Array.replicate (h+1) 0, 0, false⟩
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [:games] do
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

/-- Admission uses only the precommitted seed and fixed total game count. -/
def validateCounts (a : StatisticalCandidate) : ValidationCounts :=
  sampleCounts a validationSeed validationGames

/-- Row zero is first-turn death; subsequent rows are conditional two-turn deaths. -/
def confidenceBands (horizon : Nat) (i : Fin (horizon+1))
    (policy : FairnessPolicy := defaultPolicy) : Band :=
  ⟨if i.val = 0 then 1 - policy.survival 1 else policy.deathAtTwo (i.val-1),
   policy.tolerance⟩

/-- A row's actual denominator and observed death count. -/
def ValidationCounts.observation (c : ValidationCounts) (row : Nat) : Observation :=
  ⟨c.trials[row]!, c.deaths[row]!⟩

/-- Every interval from the complete fixed batch must fit its Weibull tolerance band. -/
def ValidationAccepted (horizon : Nat) (c : ValidationCounts)
    (policy : FairnessPolicy := defaultPolicy) : Prop :=
  c.aborted = false ∧ c.games = validationGames ∧
  c.trials.size = horizon+1 ∧ c.deaths.size = horizon+1 ∧
  ∀ i : Fin (horizon+1), c.trials[i.val]! ≤ c.games ∧
    acceptsCount (confidenceBands horizon i policy) confidenceDelta (c.observation i.val)

instance (horizon : Nat) (c : ValidationCounts) (policy : FairnessPolicy) :
    Decidable (ValidationAccepted horizon c policy) := by
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
    familyFalseAcceptance law a.truth (fun i => confidenceBands a.horizon i a.policy)
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
  · exact familyFalseAcceptance_bound law a.truth (fun i => confidenceBands a.horizon i a.policy)
      confidenceDelta valid sampling probabilities (Rat.le_of_lt confidenceLevel_valid.1)

/-- An adventure that passed admission. It holds the counts, the seed they came from, and the
proof that every row passed. `fair` says the test itself is sound; it holds for every candidate. -/
structure StatisticalAdventure where
  /-- The adventure that was checked. -/
  candidate : StatisticalCandidate
  /-- The test is sound for this candidate (true for every candidate). -/
  fair : Fair candidate
  /-- The seed of the 1,000 games. -/
  seed : Nat
  /-- The counts from those games. -/
  counts : ValidationCounts
  /-- The counts come from this candidate's own games with this seed. -/
  provenance : counts = sampleCounts candidate seed validationGames
  /-- Every row passed. -/
  accepted : ValidationAccepted candidate.horizon counts candidate.policy

/-- Every admitted interval fits its shared Weibull tolerance band. -/
theorem StatisticalAdventure.intervals_fit (a : StatisticalAdventure) (i : Fin (a.candidate.horizon+1)) :
    let count := a.counts.observation i.val
    let interval := confidenceInterval confidenceDelta count.trials count.deaths
    -- The entire interval is above the band's lower bound.
    (confidenceBands a.candidate.horizon i a.candidate.policy).target - (confidenceBands a.candidate.horizon i a.candidate.policy).tolerance ≤
      interval.lower ∧
    -- The entire interval is below the band's upper bound.
    interval.upper ≤
      (confidenceBands a.candidate.horizon i a.candidate.policy).target + (confidenceBands a.candidate.horizon i a.candidate.policy).tolerance :=
  (a.accepted.2.2.2.2 i).2.2.2

/-- Play 1,000 games of `candidate` from `seed`, and admit it only if every row passes.
Returns the counts, and the admitted adventure if it passed. -/
def admitWithSeed (candidate : StatisticalCandidate) (seed : Nat) :
    ValidationCounts × Option StatisticalAdventure :=
  let counts := sampleCounts candidate seed validationGames
  if h : ValidationAccepted candidate.horizon counts candidate.policy then
    (counts, some ⟨candidate, candidate.fair, seed, counts, rfl, h⟩)
  else (counts, none)

/-- Admission with the fixed `validationSeed`, for the Adventures shipped in this repo. -/
def admitStatistically (candidate : StatisticalCandidate) :
    ValidationCounts × Option StatisticalAdventure :=
  admitWithSeed candidate validationSeed

/-- One line for each row that failed, in plain words, for the DM and the server log.
An empty list means that every row passed. -/
def failedRows (horizon : Nat) (c : ValidationCounts) (policy : FairnessPolicy := defaultPolicy) : List String :=
  let pct (r : Rat) : String :=
    let tenths := (r * 1000).floor
    s!"{tenths / 10}.{tenths % 10}%"
  let general :=
    (if c.aborted then ["a game did not finish inside the window (a Fight went on too long)"] else []) ++
    (if c.games != validationGames then [s!"only {c.games} of {validationGames} games were played"] else [])
  general ++ (List.range (horizon + 1)).filterMap fun row =>
    if h : row < horizon + 1 then
      let i : Fin (horizon + 1) := ⟨row, h⟩
      let band := confidenceBands horizon i policy
      let obs := c.observation row
      if acceptsCount band confidenceDelta obs then none else
      let name := if row = 0 then "death on turn 1"
        else s!"death on turn {row + 1}, given alive at turn {row - 1}"
      let iv := confidenceInterval confidenceDelta obs.trials obs.deaths
      some s!"{name}: {obs.deaths} of {obs.trials} games, so {pct iv.lower} to {pct iv.upper}, but the allowed range is {pct (max 0 (band.target - band.tolerance))} to {pct (band.target + band.tolerance)}"
    else none

end Rpg.Probability
