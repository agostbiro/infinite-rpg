import Rpg.Probability.Confidence
import Rpg.Probability.Simulation
import Rpg.Probability.Continuation

/-!
Finite confidence intervals compare the adventure's conditional death expectations
with the Weibull targets of its own policy. The theorem `balanced` proves interval coverage and
bounds false acceptance under the explicitly assumed binomial sampling model.
Each candidate carries its policy. A candidate with no explicit policy uses the medium level.
-/
namespace Rpg.Probability
open Confidence

/-- Historical admission tests a point probability; live changes test two-event windows. -/
inductive BalanceProtocol where
  | point
  | window
  deriving Repr, DecidableEq, BEq

/-- An adventure and the fixed finite window chosen before validation. -/
structure StatisticalCandidate extends AdventureDefinition where
  horizon : Nat
  horizonPositive : 0 < horizon
  /-- Absent for a new Adventure; the exact revised checkpoint for live changes. -/
  resume : Option ResumePoint := none
  /-- Completed scene events before this checkpoint; never reset by a live change. -/
  elapsed : Nat := 0
  /-- A live change uses first-event death and conditional two-event windows. -/
  protocol : BalanceProtocol := .point
  /-- The target curve and tolerance that this candidate must fit. An Adventure with no
  difficulty level uses the medium level. -/
  policy : BalancePolicy := DifficultyLevel.medium.policy

/-- One timestamped check for both a new world and a changed world. -/
def StatisticalCandidate.atCheckpoint (d : AdventureDefinition) (point : ResumePoint)
    (elapsed horizon : Nat) (positive : 0 < horizon) (policy : BalancePolicy) : StatisticalCandidate :=
  { toAdventureDefinition := d, resume := some point, elapsed, horizon,
    horizonPositive := positive, policy, protocol := .window }

/-- Precommit enough trajectories for roughly 2,000 survivors at the last row of the target curve.
The 50,000-run cap bounds work; it never relaxes admission. No observed deaths select this budget. -/
def StatisticalCandidate.games (a : StatisticalCandidate) : Nat :=
  match a.protocol with
  | .point => 1200
  | .window => max 5000 (min 50000
      ((2000 : Rat) / a.policy.remainingSurvival a.elapsed (a.horizon - 1)).ceil.toNat)

/-- Every timestamped check has a bounded, nonempty precommitted batch. -/
theorem StatisticalCandidate.window_games_bounds (a : StatisticalCandidate)
    (window : a.protocol = .window) : 5000 ≤ a.games ∧ a.games ≤ 50000 := by
  simp only [games, window]
  omega

/-- The fixed, independently chosen validation seed. Never search seeds for a favorable result. -/
def validationSeed : Nat := 20261103

/-- Fixed batch size retained for historical point-probability fixtures. Live checks use `games`. -/
def difficultyGames : Nat := 1200

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

/-- Count both deaths in each window. Successful endings survive every later window. -/
def ValidationCounts.observeTrace (c : ValidationCounts) (horizon : Nat)
    (protocol : BalanceProtocol) (trace : Simulation.Trace) : ValidationCounts := Id.run do
  let mut counts := c.observe 0 (trace.finish == .dead && trace.turn == 1)
  for t in [:horizon] do
    if t < trace.turn || (protocol == .window && trace.finish == .ended) then
      let died := trace.finish == .dead &&
        (trace.turn == t+2 || (protocol == .window && trace.turn == t+1))
      counts := counts.observe (t+1) died
  return counts

/-- Collect a fixed batch for first-event death and the candidate's conditional point or window protocol.
Exploration can use a separate seed; unresolved outcomes inside the window abort the batch. -/
def sampleCounts (a : StatisticalCandidate) (seed games : Nat) : ValidationCounts := Id.run do
  let h := a.horizon
  let mut counts : ValidationCounts := ⟨Array.replicate (h+1) 0, Array.replicate (h+1) 0, 0, false⟩
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [:games] do
    let point := a.resume.getD (.scene a.story.start (a.rules.maxHP a.hero))
    let (trace, next) := (Simulation.fromPoint a.toAdventureDefinition validationRoundLimit (h+1) point).run rng
    rng := next
    counts := { counts with games := counts.games + 1 }
    if !observationsComplete h trace then
      return { counts with aborted := true }
    counts := counts.observeTrace h a.protocol trace
  return counts

/-- Admission uses only the precommitted seed and fixed total game count. -/
def validateCounts (a : StatisticalCandidate) : ValidationCounts :=
  sampleCounts a validationSeed a.games

/-- Policy parameters change the target bands, never the simulated game or combat. -/
def confidenceBandsFor (policy : BalancePolicy) (horizon : Nat) (i : Fin (horizon+1)) : Band :=
  ⟨if i.val = 0 then 1 - policy.survival 1 else policy.deathAtTwo (i.val-1), policy.tolerance⟩

/-- Later checkpoints use the same Weibull curve at the actual elapsed turn. -/
def continuationBandsFor (policy : BalancePolicy) (elapsed horizon : Nat) (i : Fin (horizon+1)) : Band :=
  if elapsed = 0 then confidenceBandsFor policy horizon i else
  ⟨if i.val = 0 then 1 - policy.survival (elapsed+1) / policy.survival elapsed
   else policy.deathAtTwo (elapsed+i.val-1), policy.tolerance⟩

/-- Checkpoint windows always use a five-point band, even for an old exempt test policy. -/
def bandsFor (protocol : BalanceProtocol) (policy : BalancePolicy)
    (elapsed horizon : Nat) (i : Fin (horizon+1)) : Band :=
  match protocol with
  | .point => continuationBandsFor policy elapsed horizon i
  | .window => ⟨policy.checkpointTarget elapsed i.val, difficultyTolerance⟩

/-- The bands of this candidate's own policy, for its finite continuation window. -/
def StatisticalCandidate.bands (a : StatisticalCandidate) : Fin (a.horizon+1) → Band :=
  bandsFor a.protocol a.policy a.elapsed a.horizon

/-- A row's actual denominator and observed death count. -/
def ValidationCounts.observation (c : ValidationCounts) (row : Nat) : Observation :=
  ⟨c.trials[row]!, c.deaths[row]!⟩

/-- Every interval from the complete fixed batch must fit its Weibull tolerance band.
The policy has no default value, so each caller names the curve that it checks against. -/
def ValidationAccepted (horizon : Nat) (c : ValidationCounts)
    (delta : Rat) (elapsed : Nat) (policy : BalancePolicy)
    (protocol : BalanceProtocol := .point) (expectedGames : Nat := difficultyGames) : Prop :=
  c.aborted = false ∧ c.games = expectedGames ∧
  c.trials.size = horizon+1 ∧ c.deaths.size = horizon+1 ∧
  ∀ i : Fin (horizon+1), c.trials[i.val]! ≤ c.games ∧
    acceptsCount (bandsFor protocol policy elapsed horizon i) delta (c.observation i.val)

instance (horizon : Nat) (c : ValidationCounts) (delta : Rat) (elapsed : Nat) (policy : BalancePolicy)
    (protocol : BalanceProtocol) (expectedGames : Nat) :
    Decidable (ValidationAccepted horizon c delta elapsed policy protocol expectedGames) := by
  unfold ValidationAccepted
  infer_instance

/-- The admission gate derives every parameter from the candidate itself. -/
def StatisticalCandidate.accepts (a : StatisticalCandidate) (counts : ValidationCounts) (delta : Rat) : Prop :=
  ValidationAccepted a.horizon counts delta a.elapsed a.policy a.protocol a.games

instance (a : StatisticalCandidate) (counts : ValidationCounts) (delta : Rat) :
    Decidable (a.accepts counts delta) := inferInstanceAs (Decidable (ValidationAccepted _ _ _ _ _ _ _))

/-- The true tested probabilities come from this candidate's own graph, not caller-supplied odds.
Zero-probability conditioning uses zero; the batch has no observations for such a row and will not admit it. -/
def StatisticalCandidate.graph (a : StatisticalCandidate) : Graph :=
  match a.resume with
  | none => a.toAdventureDefinition.graph
  | some point => continuationGraph a.toAdventureDefinition point

/-- Tested probabilities are derived from the exact starting checkpoint and rules. -/
def StatisticalCandidate.truth (a : StatisticalCandidate) (i : Fin (a.horizon+1)) : Rat :=
  if i.val = 0 then a.graph.deadBy 1
  else match a.protocol with
    | .point => (a.graph.deathAtTwo (i.val-1)).getD 0
    | .window => (a.graph.deathWithinTwo (i.val-1)).getD 0

/-- The same balance property for any adventure, start state and absolute event timestamp. -/
def StatisticalCandidate.FitsBands (a : StatisticalCandidate) : Prop :=
  ∀ i, WithinTolerance (a.truth i) (a.bands i).target (a.bands i).tolerance

instance (a : StatisticalCandidate) : Decidable a.FitsBands := by
  unfold StatisticalCandidate.FitsBands
  infer_instance

/-- An accepted batch puts the entire confidence interval inside each target band. -/
theorem StatisticalCandidate.accepted_intervals (a : StatisticalCandidate)
    (counts : ValidationCounts) (delta : Rat) (accepted : a.accepts counts delta)
    (i : Fin (a.horizon + 1)) :
    let obs := counts.observation i.val
    let iv := confidenceInterval delta obs.trials obs.deaths
    (a.bands i).target - (a.bands i).tolerance ≤ iv.lower ∧
      iv.upper ≤ (a.bands i).target + (a.bands i).tolerance :=
  (accepted.2.2.2.2 i).2.2.2

/-- Interval coverage plus admission implies the common balance property. -/
theorem StatisticalCandidate.fits_if_covered (a : StatisticalCandidate)
    (counts : ValidationCounts) (delta : Rat) (accepted : a.accepts counts delta)
    (covered : ∀ i : Fin (a.horizon + 1),
      let obs := counts.observation i.val
      let iv := confidenceInterval delta obs.trials obs.deaths
      iv.lower ≤ a.truth i ∧ a.truth i ≤ iv.upper) : a.FitsBands := by
  intro i
  exact ⟨Rat.le_trans (a.accepted_intervals counts delta accepted i).1 (covered i).1,
    Rat.le_trans (covered i).2 (a.accepted_intervals counts delta accepted i).2⟩

/-- Finite statistical balance under the accepted sampling model.
Each interval covers its true expectation with risk at most delta, and accepting all
Weibull comparisons when any tested comparison is false also has risk at most delta.
By default the comparisons use the candidate's own policy. -/
def BalancedAt (a : StatisticalCandidate) (delta : Rat) (policy : BalancePolicy := a.policy) : Prop :=
  ∀ (law : Distribution (Fin (a.horizon+1) → Observation)),
    law.Valid →
    BinomialSampling law a.truth →
    (∀ i, 0 ≤ a.truth i ∧ a.truth i ≤ 1) →
    -- Coverage holds separately for each tested conditional expectation.
    (∀ i, intervalMissProbability law a.truth delta i ≤ delta) ∧
    -- Accepting the entire finite window has false-acceptance risk at most delta.
    familyFalseAcceptance law a.truth (bandsFor a.protocol policy a.elapsed a.horizon) delta ≤ delta

/-- The public balance property uses the shared confidence level and the candidate's own policy. -/
def Balanced (a : StatisticalCandidate) : Prop := BalancedAt a confidenceDelta a.policy

/-- The main balance theorem: finite confidence intervals and Weibull-band admission are sound.
Only the stated sampling-model hypotheses are required; there are no graph or tail premises. -/
theorem StatisticalCandidate.balancedAt (a : StatisticalCandidate) (delta : Rat)
    -- Error allowances are nonnegative.
    (hd : 0 ≤ delta) (policy : BalancePolicy := a.policy) : BalancedAt a delta policy := by
  intro law valid sampling probabilities
  constructor
  -- Each interval approximates its graph-derived death-indicator expectation.
  · intro i
    exact rowConfidence law a.truth delta i sampling
      (probabilities i).1 (probabilities i).2 hd
  -- Every row must pass; a violated row bounds false acceptance of the entire decision.
  · exact familyFalseAcceptance_bound law a.truth (bandsFor a.protocol policy a.elapsed a.horizon)
      delta valid sampling probabilities hd

/-- Every candidate has the balance guarantee for its own policy, under the stated sampling
assumptions. -/
theorem StatisticalCandidate.balanced (a : StatisticalCandidate) : Balanced a :=
  a.balancedAt confidenceDelta (Rat.le_of_lt confidenceLevel_valid.1) a.policy

/-- An adventure that passed admission. It holds the counts, the seed they came from, and the
proof that every row passed. `balanced` says the test itself is sound; it holds for every candidate. -/
structure StatisticalAdventure where
  /-- The adventure that was checked. -/
  candidate : StatisticalCandidate
  /-- The test is sound for this candidate (true for every candidate). -/
  balanced : Balanced candidate
  /-- The seed of the candidate's precommitted games. -/
  seed : Nat
  /-- The counts from those games. -/
  counts : ValidationCounts
  /-- Retries can spend a smaller part of the shared error allowance. -/
  delta : Rat
  /-- A retry can strengthen confidence, but cannot weaken it. -/
  riskValid : 0 < delta ∧ delta ≤ confidenceDelta
  /-- The proof also covers the actual error allowance used by this admission. -/
  confidence : BalancedAt candidate delta
  /-- The counts come from this candidate's own games with this seed. -/
  provenance : counts = sampleCounts candidate seed candidate.games
  /-- Every row passed, against the candidate's own policy. -/
  accepted : candidate.accepts counts delta

/-- Every admitted interval fits the Weibull tolerance band of the candidate's own policy. -/
theorem StatisticalAdventure.intervals_fit (a : StatisticalAdventure) (i : Fin (a.candidate.horizon+1)) :
    let count := a.counts.observation i.val
    let interval := confidenceInterval a.delta count.trials count.deaths
    -- The entire interval is above the band's lower bound.
    (a.candidate.bands i).target - (a.candidate.bands i).tolerance ≤
      interval.lower ∧
    -- The entire interval is below the band's upper bound.
    interval.upper ≤
      (a.candidate.bands i).target + (a.candidate.bands i).tolerance :=
  a.candidate.accepted_intervals a.counts a.delta a.accepted i

/-- Play the candidate's precommitted number of games from `seed`, and admit it only if every row
fits the candidate's own policy. Returns the counts, and the admitted adventure if it passed. -/
def admitWithRisk (candidate : StatisticalCandidate) (seed : Nat) (delta : Rat) :
    ValidationCounts × Option StatisticalAdventure :=
  let counts := sampleCounts candidate seed candidate.games
  if hd : 0 < delta ∧ delta ≤ confidenceDelta then
    if h : candidate.accepts counts delta then
      (counts, some ⟨candidate, candidate.balanced, seed, counts, delta, hd,
        candidate.balancedAt delta (Rat.le_of_lt hd.1), rfl, h⟩)
    else (counts, none)
  else (counts, none)

/-- A single admission attempt uses the shared confidence setting. -/
def admitWithSeed (candidate : StatisticalCandidate) (seed : Nat) :
    ValidationCounts × Option StatisticalAdventure :=
  admitWithRisk candidate seed confidenceDelta

/-- Admission with the fixed `validationSeed`, for the Adventures shipped in this repo. -/
def admitStatistically (candidate : StatisticalCandidate) :
    ValidationCounts × Option StatisticalAdventure :=
  admitWithSeed candidate validationSeed

/-- One line for each row that failed against `policy`, in plain words, for the DM and the
server log. An empty list means that every row passed. -/
def failedRows (horizon : Nat) (c : ValidationCounts)
    (delta : Rat) (elapsed : Nat) (policy : BalancePolicy)
    (protocol : BalanceProtocol := .point) (expectedGames : Nat := difficultyGames) : List String :=
  let pct (r : Rat) : String :=
    let tenths := (r * 1000).floor
    s!"{tenths / 10}.{tenths % 10}%"
  let general :=
    (if c.aborted then ["a game did not finish inside the window (a Fight went on too long)"] else []) ++
    (if c.games != expectedGames then [s!"only {c.games} of {expectedGames} games were played"] else [])
  general ++ (List.range (horizon + 1)).filterMap fun row =>
    if h : row < horizon + 1 then
      let i : Fin (horizon + 1) := ⟨row, h⟩
      let band := bandsFor protocol policy elapsed horizon i
      let obs := c.observation row
      if acceptsCount band delta obs then none else
      let name := if row = 0 then s!"death on turn {elapsed + 1}"
        else if protocol == .window then
          s!"death within turns {elapsed + row} to {elapsed + row + 1}, given survival after turn {elapsed + row - 1}"
        else s!"death on turn {elapsed + row + 1}, given alive at turn {elapsed + row - 1}"
      let iv := confidenceInterval delta obs.trials obs.deaths
      some s!"{if band.tolerance * 2 < iv.upper - iv.lower then "Insufficient precision: " else "Not admitted: "}{name}: {obs.deaths} of {obs.trials} games, so {pct iv.lower} to {pct iv.upper}, but the allowed range is {pct (max 0 (band.target - band.tolerance))} to {pct (band.target + band.tolerance)}"
    else none

/-- Failure reports use the same timestamp, policy, window and sample budget as admission. -/
def StatisticalCandidate.failures (a : StatisticalCandidate) (counts : ValidationCounts) (delta : Rat) : List String :=
  failedRows a.horizon counts delta a.elapsed a.policy a.protocol a.games

/-- The shared check compares conditional two-event death at the supplied absolute timestamp. -/
theorem StatisticalCandidate.timestamp_target (d : AdventureDefinition) (point : ResumePoint)
    (elapsed horizon : Nat) (positive : 0 < horizon) (policy : BalancePolicy)
    (valid : policy.Valid) (offset : Nat) (within : offset + 1 < horizon + 1) :
    ((StatisticalCandidate.atCheckpoint d point elapsed horizon positive policy).bands
      ⟨offset + 1, within⟩).target =
      1 - policy.survival (elapsed + offset + 2) / policy.survival (elapsed + offset) :=
  policy.checkpointTarget_pair valid elapsed offset

end Rpg.Probability
