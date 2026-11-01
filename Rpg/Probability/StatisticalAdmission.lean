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

/-- Historical batch size retained for saved policies. -/
def validationGames : Nat := 1000

/-- Fixed batch size selected before testing; strict late-window estimates need more survivors. -/
def validationGamesFor (policy : FairnessPolicy) : Nat :=
  if policy.protocol == .twoEventWindow then 5000 else validationGames

/-- Combat timeouts abort validation rather than selecting only completed fights. -/
def validationRoundLimit : Nat := 200

/-- First-turn death, horizon conditional windows, and a ten-turn check for new Wishes. -/
def validationRows (horizon : Nat) (policy : FairnessPolicy) : Nat :=
  horizon + 1 + if policy.protocol == .twoEventWindow then 1 else 0

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

/-- Record a complete trace using the policy's conditioning event.
Successful endings have infinite death time and remain survivors in window tests. -/
def ValidationCounts.observeTrace (c : ValidationCounts) (horizon : Nat)
    (policy : FairnessPolicy) (trace : Simulation.Trace) : ValidationCounts := Id.run do
  let mut counts := c.observe 0 (trace.finish == .dead && trace.turn == 1)
  for t in [:horizon] do
    let window := policy.protocol == .twoEventWindow
    if t < trace.turn || (window && trace.finish == .ended) then
      let died := trace.finish == .dead &&
        (trace.turn == t+2 || (window && trace.turn == t+1))
      counts := counts.observe (t+1) died
  if policy.protocol == .twoEventWindow then
    counts := counts.observe (horizon+1) (trace.finish == .dead && trace.turn ≤ 10)
  return counts

/-- Collect a fixed batch without discarding unresolved outcomes.
New policies always simulate enough choices to observe death by ten. -/
def sampleCounts (a : StatisticalCandidate) (seed games : Nat) : ValidationCounts := Id.run do
  let h := a.horizon
  let window := a.policy.protocol == .twoEventWindow
  let observationHorizon := if window then max 9 h else h
  let rows := validationRows h a.policy
  let mut counts : ValidationCounts := ⟨Array.replicate rows 0, Array.replicate rows 0, 0, false⟩
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [:games] do
    let (trace, next) := (Simulation.trajectory a.toAdventureDefinition validationRoundLimit
      (observationHorizon+1) a.story.start (a.rules.maxHP a.hero) 0).run rng
    rng := next
    counts := { counts with games := counts.games + 1 }
    if !observationsComplete observationHorizon trace then
      return { counts with aborted := true }
    counts := counts.observeTrace h a.policy trace
  return counts

/-- Recover exact-turn counts before summing overlapping two-event windows. -/
def ValidationCounts.deathsPerTurn (c : ValidationCounts) (policy : FairnessPolicy) : Array Nat :=
  if policy.protocol == .legacyPoint then c.deaths else Id.run do
    let mut previous := 0
    let mut exactCounts := #[]
    for window in c.deaths.pop do
      let current := window - previous
      exactCounts := exactCounts.push current
      previous := current
    return exactCounts

/-- Admission uses only the precommitted seed and fixed total game count. -/
def validateCounts (a : StatisticalCandidate) : ValidationCounts :=
  sampleCounts a validationSeed (validationGamesFor a.policy)

/-- Row zero tests first-turn death. The final new-protocol row tests death by ten. -/
def confidenceBand (horizon row : Nat) (policy : FairnessPolicy) : Band :=
  ⟨if row = 0 then 1 - policy.survival 1
   else if policy.protocol == .twoEventWindow && row == horizon+1 then 1 - policy.survival 10
   else policy.deathTarget (row-1), policy.tolerance⟩

/-- The finite family of bands used by the statistical theorem. -/
def confidenceBands (horizon : Nat) (policy : FairnessPolicy)
    (i : Fin (validationRows horizon policy)) : Band :=
  confidenceBand horizon i.val policy

/-- A row's actual denominator and observed death count. -/
def ValidationCounts.observation (c : ValidationCounts) (row : Nat) : Observation :=
  ⟨c.trials[row]!, c.deaths[row]!⟩

/-- Every interval from the complete fixed batch must fit its Weibull tolerance band. -/
def ValidationAccepted (horizon : Nat) (c : ValidationCounts)
    (policy : FairnessPolicy := defaultPolicy) : Prop :=
  c.aborted = false ∧ c.games = validationGamesFor policy ∧
  c.trials.size = validationRows horizon policy ∧ c.deaths.size = validationRows horizon policy ∧
  ∀ i : Fin (validationRows horizon policy), c.trials[i.val]! ≤ c.games ∧
    acceptsCount (confidenceBands horizon policy i) policy.testRisk (c.observation i.val)

instance (horizon : Nat) (c : ValidationCounts) (policy : FairnessPolicy) :
    Decidable (ValidationAccepted horizon c policy) := by
  unfold ValidationAccepted
  infer_instance

/-- The true tested probabilities come from this candidate's own graph, not caller-supplied odds.
Zero-probability conditioning uses zero; the batch has no observations for such a row and will not admit it. -/
def StatisticalCandidate.truth (a : StatisticalCandidate) (i : Fin (validationRows a.horizon a.policy)) : Rat :=
  if i.val = 0 then a.toAdventureDefinition.graph.deadBy 1
  else if a.policy.protocol == .twoEventWindow && i.val == a.horizon+1 then
    a.toAdventureDefinition.graph.deadBy 10
  else (a.toAdventureDefinition.graph.conditionalDeath a.policy (i.val-1)).getD 0

/-- Finite statistical fairness under the accepted sampling model.
Each interval covers its true expectation with risk at most delta, and accepting all
Weibull comparisons when any tested comparison is false also has risk at most delta. -/
def Fair (a : StatisticalCandidate) : Prop :=
  ∀ (law : Distribution (Fin (validationRows a.horizon a.policy) → Observation)),
    law.Valid →
    BinomialSampling law a.truth →
    (∀ i, 0 ≤ a.truth i ∧ a.truth i ≤ 1) →
    -- Coverage holds separately for each tested conditional expectation.
    (∀ i, intervalMissProbability law a.truth a.policy.testRisk i ≤ a.policy.testRisk) ∧
    -- Accepting the entire finite window has false-acceptance risk at most delta.
    familyFalseAcceptance law a.truth (fun i => confidenceBands a.horizon a.policy i)
      a.policy.testRisk ≤ a.policy.testRisk

/-- The main fairness theorem: finite confidence intervals and Weibull-band admission are sound.
Only the stated sampling-model hypotheses are required; there are no graph or tail premises. -/
theorem StatisticalCandidate.fair (a : StatisticalCandidate) : Fair a := by
  intro law valid sampling probabilities
  constructor
  -- Each interval approximates its graph-derived death-indicator expectation.
  · intro i
    exact rowConfidence law a.truth a.policy.testRisk i sampling
      (probabilities i).1 (probabilities i).2 (Rat.le_of_lt a.policy.testRisk_valid.1)
  -- Every row must pass; a violated row bounds false acceptance of the entire decision.
  · exact familyFalseAcceptance_bound law a.truth (fun i => confidenceBands a.horizon a.policy i)
      a.policy.testRisk valid sampling probabilities (Rat.le_of_lt a.policy.testRisk_valid.1)

/-- An adventure that passed admission. It holds the counts, the seed they came from, and the
proof that every row passed. `fair` says the test itself is sound; it holds for every candidate. -/
structure StatisticalAdventure where
  /-- The adventure that was checked. -/
  candidate : StatisticalCandidate
  /-- The test is sound for this candidate (true for every candidate). -/
  fair : Fair candidate
  /-- The seed of the precommitted batch. -/
  seed : Nat
  /-- The counts from those games. -/
  counts : ValidationCounts
  /-- The counts come from this candidate's own games with this seed. -/
  provenance : counts = sampleCounts candidate seed (validationGamesFor candidate.policy)
  /-- Every row passed. -/
  accepted : ValidationAccepted candidate.horizon counts candidate.policy

/-- Every admitted interval fits its shared Weibull tolerance band. -/
theorem StatisticalAdventure.intervals_fit (a : StatisticalAdventure) (i : Fin (validationRows a.candidate.horizon a.candidate.policy)) :
    let count := a.counts.observation i.val
    let interval := confidenceInterval a.candidate.policy.testRisk count.trials count.deaths
    -- The entire interval is above the band's lower bound.
    (confidenceBands a.candidate.horizon a.candidate.policy i).target - (confidenceBands a.candidate.horizon a.candidate.policy i).tolerance ≤
      interval.lower ∧
    -- The entire interval is below the band's upper bound.
    interval.upper ≤
      (confidenceBands a.candidate.horizon a.candidate.policy i).target + (confidenceBands a.candidate.horizon a.candidate.policy i).tolerance :=
  (a.accepted.2.2.2.2 i).2.2.2

/-- Play the policy's fixed batch from `seed`, and admit only if every row passes.
Returns the counts, and the admitted adventure if it passed. -/
def admitWithSeed (candidate : StatisticalCandidate) (seed : Nat) :
    ValidationCounts × Option StatisticalAdventure :=
  let counts := sampleCounts candidate seed (validationGamesFor candidate.policy)
  if h : ValidationAccepted candidate.horizon counts candidate.policy then
    (counts, some ⟨candidate, candidate.fair, seed, counts, rfl, h⟩)
  else (counts, none)

/-- Admission with the fixed `validationSeed`, for the Adventures shipped in this repo. -/
def admitStatistically (candidate : StatisticalCandidate) :
    ValidationCounts × Option StatisticalAdventure :=
  admitWithSeed candidate validationSeed

/-- Diagnostic only: distinguish insufficient precision from an interval outside the band.
Only `ValidationAccepted` can admit a game. -/
def intervalStatus (band : Band) (count : Observation) (iv : Interval) : String :=
  if count.trials == 0 then "inconclusive"
  else if count.deaths > count.trials then "invalid"
  else if band.target-band.tolerance ≤ iv.lower && iv.upper ≤ band.target+band.tolerance then
    "accepted"
  else if iv.upper < band.target-band.tolerance || band.target+band.tolerance < iv.lower then
    "outside-band"
  else "inconclusive"

/-- One line for each row that failed, in plain words, for the DM and the server log.
An empty list means that every row passed. -/
def failedRows (horizon : Nat) (c : ValidationCounts) (policy : FairnessPolicy := defaultPolicy) : List String :=
  let pct (r : Rat) : String :=
    let tenths := (r * 1000).floor
    s!"{tenths / 10}.{tenths % 10}%"
  let general :=
    (if c.aborted then ["a game did not finish inside the window (a Fight went on too long)"] else []) ++
    (if c.games != validationGamesFor policy then [s!"only {c.games} of {validationGamesFor policy} games were played"] else [])
  general ++ (List.range (validationRows horizon policy)).filterMap fun row =>
    if h : row < validationRows horizon policy then
      let i : Fin (validationRows horizon policy) := ⟨row, h⟩
      let band := confidenceBands horizon policy i
      let obs := c.observation row
      let iv := confidenceInterval policy.testRisk obs.trials obs.deaths
      let status := intervalStatus band obs iv
      if status == "accepted" then none else
      let name := if row = 0 then "death on turn 1"
        else if policy.protocol == .twoEventWindow && row == horizon+1 then "death by turn 10"
        else if policy.protocol == .twoEventWindow then
          s!"death within turns {row} to {row + 1}, given survival after turn {row - 1}"
        else s!"death on turn {row + 1}, given active after turn {row - 1}"
      some s!"{status}: {name}: {obs.deaths} of {obs.trials} games, so {pct iv.lower} to {pct iv.upper}, but the allowed range is {pct (max 0 (band.target - band.tolerance))} to {pct (band.target + band.tolerance)}"
    else none

end Rpg.Probability
