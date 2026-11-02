import Rpg.Probability.Confidence
import Rpg.Probability.Simulation
import Rpg.Probability.AdventureCertificate
import Rpg.EventGraph

/-!
Finite confidence intervals compare the adventure's conditional death expectations
with the Weibull targets of its own policy. The theorem `balanced` proves interval coverage and
bounds false acceptance under the explicitly assumed binomial sampling model.
Each candidate carries its policy. Every candidate in the game uses `defaultPolicy`.
-/
namespace Rpg.Probability
open Confidence

/-- An adventure and the fixed finite window chosen before validation. -/
structure StatisticalCandidate extends AdventureDefinition where
  horizon : Nat
  horizonPositive : 0 < horizon
  /-- Absent for adventure admission; optional for separate continuation analysis. -/
  resume : Option ResumePoint := none
  /-- Elapsed scene turns for optional continuation analysis; admission starts at zero. -/
  elapsed : Nat := 0
  /-- The target curve and tolerance that this candidate must fit. The game always uses
  `defaultPolicy`. -/
  policy : BalancePolicy := defaultPolicy

/-- The fixed, independently chosen validation seed. Never search seeds for a favorable result. -/
def validationSeed : Nat := 20261103

/-- The number of games in one balance check. It is a precommitted batch size, not a number of
qualifying observations per row. -/
def validationGames : Nat := 1200

/-- Combat timeouts abort validation rather than selecting only completed fights. -/
def validationRoundLimit : Nat := 200

/-- Counts from the same fixed game batch; later rows can have fewer qualifying games. -/
structure ValidationCounts where
  trials : Array Nat
  deaths : Array Nat
  games : Nat := 0
  aborted : Bool := false
  /-- Mandatory structural or combat evidence failed. -/
  combatRejected : Bool := false
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
  let mut counts : ValidationCounts := ⟨Array.replicate (h+1) 0, Array.replicate (h+1) 0, 0, false, false⟩
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [:games] do
    let point := a.resume.getD (.scene a.story.start (a.rules.maxHP a.hero))
    let (trace, next) := (Simulation.fromPoint a.toAdventureDefinition validationRoundLimit (h+1) point).run rng
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

/-- Policy parameters change the target bands, never the simulated game or combat. -/
def confidenceBandsFor (policy : BalancePolicy) (horizon : Nat) (i : Fin (horizon+1)) : Band :=
  ⟨if i.val = 0 then 1 - policy.survival 1 else policy.deathAtTwo (i.val-1), policy.tolerance⟩

/-- Later checkpoints use the same Weibull curve at the actual elapsed turn. -/
def continuationBandsFor (policy : BalancePolicy) (elapsed horizon : Nat) (i : Fin (horizon+1)) : Band :=
  if elapsed = 0 then confidenceBandsFor policy horizon i else
  ⟨if i.val = 0 then 1 - policy.survival (elapsed+1) / policy.survival elapsed
   else policy.deathAtTwo (elapsed+i.val-1), policy.tolerance⟩

/-- The bands of this candidate's own policy, for its finite continuation window. -/
def StatisticalCandidate.bands (a : StatisticalCandidate) : Fin (a.horizon+1) → Band :=
  continuationBandsFor a.policy a.elapsed a.horizon

/-- A row's actual denominator and observed death count. -/
def ValidationCounts.observation (c : ValidationCounts) (row : Nat) : Observation :=
  ⟨c.trials[row]!, c.deaths[row]!⟩

/-- Every interval from the complete fixed batch must fit its Weibull tolerance band.
The policy has no default value, so each caller names the curve that it checks against. -/
def ValidationAccepted (horizon : Nat) (c : ValidationCounts)
    (delta : Rat) (elapsed : Nat) (policy : BalancePolicy) : Prop :=
  c.aborted = false ∧ c.games = validationGames ∧
  c.trials.size = horizon+1 ∧ c.deaths.size = horizon+1 ∧
  ∀ i : Fin (horizon+1), c.trials[i.val]! ≤ c.games ∧
    acceptsCount (continuationBandsFor policy elapsed horizon i) delta (c.observation i.val)

instance (horizon : Nat) (c : ValidationCounts) (delta : Rat) (elapsed : Nat) (policy : BalancePolicy) :
    Decidable (ValidationAccepted horizon c delta elapsed policy) := by
  unfold ValidationAccepted
  infer_instance

/-- The true tested probabilities come from this candidate's own graph, not caller-supplied odds.
Zero-probability conditioning uses zero; the batch has no observations for such a row and will not admit it. -/
def StatisticalCandidate.graph (a : StatisticalCandidate) : Graph :=
  match a.resume with
  | none => a.toAdventureDefinition.graph
  | some point => continuationGraph a.toAdventureDefinition point

/-- Tested probabilities are derived from the exact starting checkpoint and rules. -/
def StatisticalCandidate.truth (a : StatisticalCandidate) (i : Fin (a.horizon+1)) : Rat :=
  if i.val = 0 then a.graph.deadBy 1
  else (a.graph.deathAtTwo (i.val-1)).getD 0

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
    familyFalseAcceptance law a.truth (continuationBandsFor policy a.elapsed a.horizon) delta ≤ delta

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
  · exact familyFalseAcceptance_bound law a.truth (continuationBandsFor policy a.elapsed a.horizon)
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
  /-- Admission covers the original adventure; continuation analysis is separate. -/
  fromStart : candidate.resume = none ∧ candidate.elapsed = 0
  shortLoops : candidate.story.NoShortLoops
  combat : CertifiedAdventureCombat candidate.toAdventureDefinition
  /-- The seed of the `validationGames` games. -/
  seed : Nat
  /-- The counts from those games. -/
  counts : ValidationCounts
  /-- Retries can spend a smaller part of the shared error allowance. -/
  delta : Rat
  /-- A retry can strengthen confidence, but cannot weaken it. -/
  riskValid : 0 < delta ∧ delta ≤ confidenceDelta
  /-- The counts come from this candidate's own games with this seed. -/
  provenance : counts = sampleCounts candidate seed validationGames
  /-- Every row passed, against the candidate's own policy. -/
  accepted : ValidationAccepted candidate.horizon counts delta candidate.elapsed candidate.policy

/-- Generic soundness is derived, rather than stored redundantly in every admitted value. -/
theorem StatisticalAdventure.balanced (a : StatisticalAdventure) : Balanced a.candidate :=
  a.candidate.balanced

theorem StatisticalAdventure.confidence (a : StatisticalAdventure) : BalancedAt a.candidate a.delta :=
  a.candidate.balancedAt a.delta (Rat.le_of_lt a.riskValid.1)

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
  (a.accepted.2.2.2.2 i).2.2.2

/-- Play `validationGames` games of `candidate` from `seed`, and admit it only if every row
fits the candidate's own policy. Returns the counts, and the admitted adventure if it passed. -/
def admitWithRisk (candidate : StatisticalCandidate) (seed : Nat) (delta : Rat) :
    ValidationCounts × Option StatisticalAdventure :=
  let counts := sampleCounts candidate seed validationGames
  if hd : 0 < delta ∧ delta ≤ confidenceDelta then
    if h : ValidationAccepted candidate.horizon counts delta candidate.elapsed candidate.policy then
      if hs : candidate.resume = none ∧ candidate.elapsed = 0 then
      if hl : candidate.story.NoShortLoops then
        match certifyAdventureCombat candidate.toAdventureDefinition with
        | some combat => (counts, some ⟨candidate,hs,hl,combat,seed,counts,delta,hd,rfl,h⟩)
        | none => ({counts with combatRejected := true}, none)
      else ({counts with combatRejected := true}, none)
      else ({counts with combatRejected := true}, none)
    else (counts, none)
  else (counts, none)

/-- An admitted Adventure is about the candidate that was checked. -/
theorem admitWithRisk_candidate {c : StatisticalCandidate} {seed : Nat} {delta : Rat}
    {counts : ValidationCounts} {a : StatisticalAdventure}
    -- The check admitted `a`.
    (h : admitWithRisk c seed delta = (counts, some a)) :
    -- `a` is about the candidate `c`.
    a.candidate = c := by
  unfold admitWithRisk at h
  dsimp only at h
  repeat split at h
  all_goals simp_all
  all_goals rw [← h.2]

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
    (delta : Rat) (elapsed : Nat) (policy : BalancePolicy) : List String :=
  let pct (r : Rat) : String :=
    let tenths := (r * 1000).floor
    s!"{tenths / 10}.{tenths % 10}%"
  let general :=
    (if c.combatRejected then ["admission certification failed: invalid checkpoint, short loop, or unverified combat"] else []) ++
    (if c.aborted then ["a game did not finish inside the window (a Fight went on too long)"] else []) ++
    (if c.games != validationGames then [s!"only {c.games} of {validationGames} games were played"] else [])
  general ++ (List.range (horizon + 1)).filterMap fun row =>
    if h : row < horizon + 1 then
      let i : Fin (horizon + 1) := ⟨row, h⟩
      let band := continuationBandsFor policy elapsed horizon i
      let obs := c.observation row
      if acceptsCount band delta obs then none else
      let name := if row = 0 then s!"death on turn {elapsed + 1}"
        else s!"death on turn {elapsed + row + 1}, given alive at turn {elapsed + row - 1}"
      let iv := confidenceInterval delta obs.trials obs.deaths
      some s!"{name}: {obs.deaths} of {obs.trials} games, so {pct iv.lower} to {pct iv.upper}, but the allowed range is {pct (max 0 (band.target - band.tolerance))} to {pct (band.target + band.tolerance)}"
    else none

end Rpg.Probability
