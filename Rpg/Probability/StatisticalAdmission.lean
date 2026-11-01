import Rpg.Probability.Confidence
import Rpg.Probability.Estimate

/-!
A statistical admission is a different claim from an exact `isFair` proof.
It carries a source-bound audit, rational acceptance checks, a finite route bound,
and a proved false-acceptance bound under the explicitly stated binomial sampling model.
The model assumes independent ideal trajectories; the seeded PRNG is not proved IID.
-/
namespace Rpg.Probability
open Confidence

/-- A sequence of actual scene links; death and stalled combat stop making scene links. -/
inductive SceneWalk (story : Adventure) : SceneId → Nat → SceneId → Prop where
  | stay (scene : SceneId) : SceneWalk story scene 0 scene
  | step {first next last length} : Leads story first next →
      SceneWalk story next length last → SceneWalk story first (length + 1) last

/-- Every actual outcome target decreases the adventure's natural-number rank. -/
def DecreasingRanks (story : Adventure) (rank : SceneId → Nat) : Prop :=
  ∀ scene ∈ story.scenes, ∀ choice ∈ scene.choices,
    ∀ target ∈ choice.outcome.targets, rank target < rank scene.id

/-- No route can make more scene choices than its initial rank. -/
theorem sceneWalk_bound (decreasing : DecreasingRanks story rank)
    (walk : SceneWalk story first length last) : length + rank last ≤ rank first := by
  induction walk with
  | stay scene => omega
  | step lead _ ih =>
    obtain ⟨scene, hs, hid, choice, hc, ht⟩ := lead
    have down := decreasing scene hs choice hc _ ht
    subst hid
    omega

/-- The experiment's story, rules and hero, plus a proof that its route horizon is sufficient. -/
structure StatisticalCandidate extends AdventureDefinition where
  rank : SceneId → Nat
  decreasing : DecreasingRanks story rank
  horizonPositive : 0 < rank story.start

/-- Maximum possible number of scene choices, including a terminating fight. -/
def StatisticalCandidate.horizon (a : StatisticalCandidate) : Nat := a.rank a.story.start

/-- The fixed, independently chosen validation seed. Never search seeds for a favorable result. -/
def validationSeed : Nat := 20261102

/-- A finite computation budget; exhausting it cannot result in admission. -/
def validationMaxGames : Nat := 2000000

/-- Combat timeouts abort validation rather than selecting only completed fights. -/
def validationRoundLimit : Nat := 200

/-- Counts take only the first required qualifying observations in each row. -/
structure ValidationCounts where
  trials : Array Nat
  deaths : Array Nat
  games : Nat := 0
  aborted : Bool := false
  deriving Repr

/-- Add one Bernoulli observation unless this row already has its fixed sample size. -/
def ValidationCounts.observe (c : ValidationCounts) (row : Nat) (death : Bool) : ValidationCounts :=
  if c.trials[row]! ≥ confidenceSamples then c
  else { c with
    trials := c.trials.modify row (· + 1)
    deaths := c.deaths.modify row (· + if death then 1 else 0) }

/-- Rejection sampling for active-at-t rows. It never stops based on observed death rates.
Any censored or invalid trajectory aborts; insufficient qualifying counts cannot pass. -/
def validateCounts (a : StatisticalCandidate) : ValidationCounts := Id.run do
  let h := a.horizon
  let mut counts : ValidationCounts := ⟨Array.replicate (h+1) 0, Array.replicate (h+1) 0, 0, false⟩
  let mut rng : Rng := ⟨validationSeed.toUInt64⟩
  for _ in [:validationMaxGames] do
    if counts.trials.all (· == confidenceSamples) then break
    let (trace, next) := (Estimate.trajectory a.toAdventureDefinition validationRoundLimit (h+2)
      a.story.start (a.rules.maxHP a.hero) 0).run rng
    rng := next
    counts := { counts with games := counts.games + 1 }
    if trace.finish == .censored || trace.finish == .invalid then
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

/-- An exact rational check on the full audit result, including completion and all rows. -/
def ValidationAccepted (horizon : Nat) (c : ValidationCounts) : Prop :=
  c.aborted = false ∧ c.trials.size = horizon+1 ∧ c.deaths.size = horizon+1 ∧
  ∀ i : Fin (horizon+1), c.trials[i.val]! = confidenceSamples ∧
    c.deaths[i.val]! ≤ confidenceSamples ∧
    acceptsCount (confidenceBands horizon i).target (confidenceBands horizon i).tolerance
      confidenceEpsilon confidenceSamples c.deaths[i.val]!

instance (horizon : Nat) (c : ValidationCounts) : Decidable (ValidationAccepted horizon c) := by
  unfold ValidationAccepted
  infer_instance

/-- Source-bound evidence. This is a statistical certificate, NOT `CertifiedAdventure`.
The provenance equality prevents importing counts from a different story or ruleset. -/
structure StatisticalAdventure where
  candidate : StatisticalCandidate
  counts : ValidationCounts
  provenance : counts = validateCounts candidate
  accepted : ValidationAccepted candidate.horizon counts

/-- An admitted observation satisfies every numerical constraint in the confidence theorem. -/
theorem StatisticalAdventure.accepts (a : StatisticalAdventure) :
    acceptsFamily (confidenceBands a.candidate.horizon) confidenceEpsilon confidenceSamples
      (fun i => a.counts.deaths[i.val]!) := by
  intro i
  exact (a.accepted.2.2.2 i).2.2

/-- The true tested probabilities come from this candidate's own graph, not caller-supplied odds.
Zero-probability conditioning uses zero; the audit cannot fill such a row and will not admit it. -/
def StatisticalCandidate.truth (a : StatisticalCandidate) (i : Fin (a.horizon+1)) : Rat :=
  if i.val = 0 then a.toAdventureDefinition.graph.deadBy 1
  else (a.toAdventureDefinition.graph.deathAtTwo (i.val-1)).getD 0

/-- The tuned geometric policy has a constant two-turn target. -/
theorem geometricTarget (t : Nat) : defaultPolicy.deathAtTwo t = (4/25 : Rat) := by
  have positive : (0 : Rat) < (4/5 : Rat)^t := Rat.pow_pos (by decide +kernel)
  have nz : (4/5 : Rat)^t ≠ 0 := by grind
  simp only [FairnessPolicy.deathAtTwo, FairnessPolicy.survival, defaultPolicy,
    weibullShape, weibullRetention, Nat.pow_one, Rat.pow_succ]
  grind

/-- Once no further deaths are possible, the new policy's two-turn bound is satisfied. -/
theorem zero_death_tail (t : Nat) : WithinTolerance 0 (defaultPolicy.deathAtTwo t) defaultPolicy.tolerance := by
  rw [geometricTarget]
  decide +kernel

/-- The fairness-confidence theorem used by statistical admissions.
Its conclusion is a false-certification risk bound under an explicit sampling law,
not a posterior probability of fairness or an unconditional claim about SplitMix64. -/
theorem StatisticalCandidate.fairnessConfidence (a : StatisticalCandidate)
    (law : Distribution (Fin (a.horizon+1) → Nat))
    (valid : law.Valid)
    (sampling : BinomialMarginals law a.truth confidenceSamples)
    (probabilities : ∀ i, 0 ≤ a.truth i ∧ a.truth i ≤ 1) :
    familyFalseAcceptance law a.truth (confidenceBands a.horizon)
      confidenceEpsilon confidenceSamples ≤ confidenceDelta :=
  familyFairnessConfidence law a.truth (confidenceBands a.horizon)
    confidenceEpsilon confidenceDelta confidenceSamples valid sampling probabilities
    (by decide) (by decide +kernel) (by decide +kernel) confidenceBudget

/-- Tested constraints plus a deterministic tail bound imply the original all-time predicate.
Graph normalization and the initial-state condition remain explicit model obligations. -/
theorem StatisticalCandidate.testedAndTail (a : StatisticalCandidate)
    (validGraph : a.toAdventureDefinition.graph.Valid)
    (activeStart : a.toAdventureDefinition.graph.activeAt 0 = 1)
    (tailFair : ∀ t actual, a.horizon ≤ t → a.toAdventureDefinition.graph.deathAtTwo t = some actual →
      WithinTolerance actual (defaultPolicy.deathAtTwo t) defaultPolicy.tolerance)
    (tested : familyFair a.truth (confidenceBands a.horizon)) :
    isFair defaultPolicy a.toAdventureDefinition.graph := by
  refine ⟨defaultPolicy_valid, validGraph, activeStart, ?_, ?_⟩
  · have first := tested ⟨0, Nat.zero_lt_succ _⟩
    simpa [StatisticalCandidate.truth, confidenceBands] using first
  · intro t actual observed
    by_cases before : t < a.horizon
    · have row := tested ⟨t+1, Nat.succ_lt_succ before⟩
      simpa [StatisticalCandidate.truth, confidenceBands, observed] using row
    · exact tailFair t actual (by omega) observed

/-- Probability of approving a sample while the original all-time fairness predicate is false. -/
noncomputable def StatisticalCandidate.falseAllTimeAcceptance (a : StatisticalCandidate)
    (law : Distribution (Fin (a.horizon+1) → Nat)) : Rat := by
  classical
  exact expectation law fun counts =>
    if acceptsFamily (confidenceBands a.horizon) confidenceEpsilon confidenceSamples counts ∧
        ¬ isFair defaultPolicy a.toAdventureDefinition.graph then 1 else 0

/-- All-time fairness-confidence guarantee when the graph/tail and sampling obligations are met.
No observed frequency is used as a proof of a true probability. -/
theorem StatisticalCandidate.allTimeFairnessConfidence (a : StatisticalCandidate)
    (law : Distribution (Fin (a.horizon+1) → Nat))
    (valid : law.Valid) (sampling : BinomialMarginals law a.truth confidenceSamples)
    (probabilities : ∀ i, 0 ≤ a.truth i ∧ a.truth i ≤ 1)
    (validGraph : a.toAdventureDefinition.graph.Valid)
    (activeStart : a.toAdventureDefinition.graph.activeAt 0 = 1)
    (tailFair : ∀ t actual, a.horizon ≤ t → a.toAdventureDefinition.graph.deathAtTwo t = some actual →
      WithinTolerance actual (defaultPolicy.deathAtTwo t) defaultPolicy.tolerance) :
    a.falseAllTimeAcceptance law ≤ confidenceDelta := by
  classical
  have bound : a.falseAllTimeAcceptance law ≤
      familyFalseAcceptance law a.truth (confidenceBands a.horizon) confidenceEpsilon confidenceSamples := by
    apply expectation_monotone law valid.1
    intro counts
    split
    · next accepted =>
      have bad : ¬ familyFair a.truth (confidenceBands a.horizon) := by
        intro good
        exact accepted.2 (a.testedAndTail validGraph activeStart tailFair good)
      simp only [accepted.1, bad]
      exact Rat.le_refl
    · split <;> decide +kernel
  exact Rat.le_trans bound (a.fairnessConfidence law valid sampling probabilities)

/-- Audit current inputs and admit only a completed, passing result. No data is pre-authorized. -/
def admitStatistically (candidate : StatisticalCandidate) :
    ValidationCounts × Option StatisticalAdventure :=
  let counts := validateCounts candidate
  if h : ValidationAccepted candidate.horizon counts then
    (counts, some ⟨candidate, counts, rfl, h⟩)
  else (counts, none)

end Rpg.Probability
