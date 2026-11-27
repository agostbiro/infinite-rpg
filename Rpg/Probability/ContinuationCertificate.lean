import Rpg.Probability.AdventureCertificate
import Rpg.Game

/-! Certification at a paused Character turn. The first step completes only the
unfinished part of this round; later steps are full rounds. -/
namespace Rpg.Probability

def remainingDistribution (rules : RuleSet) (f : FightPhase) : Distribution FightState :=
  (Prod.fst <$> remainingRoundWith (attackDistribution rules) heroPolicy f.order f.state).collect

theorem remainingDistribution_valid (rules : RuleSet) (f : FightPhase) :
    (remainingDistribution rules f).Valid :=
  Distribution.valid_collect _ (Distribution.valid_map _ _ (remainingRound_valid rules f.order f.state))

def continuationProcess (rules : RuleSet) (f : FightPhase) : StoppingProcess (Option FightState) where
  terminal s := match s with | none => false | some s => s.over
  step s := match s with
    | none => some <$> remainingDistribution rules f
    | some s => some <$> (combatProcess rules f.order).step s
  valid s := by
    cases s
    · exact Distribution.valid_map _ _ (remainingDistribution_valid rules f)
    · exact Distribution.valid_map _ _ ((combatProcess rules f.order).valid _)

/-- The rest of a round paused at the Character's turn, with `heroPolicy` and `fastAttack`. Like
`fastRound`, it merges equal states after each turn. -/
def fastRemaining (rules : RuleSet) (order : List Actor) (s : FightState) :
    Distribution FightState :=
  if s.over then pure s else
  let mine := ((heroPolicy s).bind fun (m, t) =>
    Prod.fst <$> heroTurnWith (fastAttack rules) s m t).sortCollect stateKey
  (mine.bind fun s => fastFoes rules s (afterCharacter order)).sortCollect stateKey

/-- For every observable of the state after the paused round, `fastRemaining` and
`remainingDistribution` give the same expected value. -/
theorem fastRemaining_expect (rules : RuleSet) (f : FightPhase) (observe : FightState → Rat) :
    (fastRemaining rules f.order f.state).expect observe =
      (remainingDistribution rules f).expect observe := by
  simp only [remainingDistribution, Distribution.expect_collect, Distribution.expect_map]
  rw [remaining_forgets (fastAttack_forgets rules) heroPolicy f.order f.state observe]
  simp only [fastRemaining, remainingRoundWith, Bind.bind]
  split
  -- The Fight is already over.
  · rfl
  -- The Character acts, then the Creatures after it.
  · simp only [Distribution.expect_sortCollect, Distribution.expect_bind, Distribution.expect_map,
      Distribution.expect_pure]
    congr 1
    funext choice
    congr 1
    funext mine
    exact fastFoes_correct rules mine.1 (afterCharacter f.order) observe

/-- `fastRemaining` is a probability distribution. -/
theorem fastRemaining_valid (rules : RuleSet) (order : List Actor) (s : FightState) :
    (fastRemaining rules order s).Valid := by
  unfold fastRemaining
  split
  -- The Fight is over and stays as it is.
  · exact Distribution.valid_pure _
  -- The Character acts, then the Creatures after it.
  · next hs =>
    apply Distribution.valid_sortCollect
    apply Distribution.valid_bind
    -- The Character's turn.
    · apply Distribution.valid_sortCollect
      apply Distribution.valid_bind _ _ (heroPolicy_valid s (Bool.eq_false_iff.mpr hs))
      intro choice
      exact Distribution.valid_map _ _ (heroTurnWith_valid (fastAttack_valid rules) _ _ _)
    -- The Creatures after the Character.
    · intro u
      exact fastFoes_valid _ _ _

/-- The checker's version of `continuationProcess`: the paused round uses `fastRemaining`, and
the full rounds use `fastProcess`. -/
def fastContinuationProcess (rules : RuleSet) (f : FightPhase) :
    StoppingProcess (Option FightState) where
  terminal s := match s with | none => false | some s => s.over
  step s := match s with
    | none => some <$> fastRemaining rules f.order f.state
    | some s => some <$> (fastProcess rules f.order).step s
  valid s := by
    cases s
    -- Before the paused round: the rest of that round.
    · exact Distribution.valid_map _ _ (fastRemaining_valid rules f.order f.state)
    -- A state of the Fight: one full round.
    · exact Distribution.valid_map _ _ ((fastProcess rules f.order).valid _)

/-- The checker's process has the odds of `continuationProcess`. -/
theorem fastContinuation_sameOdds (rules : RuleSet) (f : FightPhase) :
    (fastContinuationProcess rules f).SameOdds (continuationProcess rules f) where
  terminal := rfl
  step s g ht := by
    cases s with
    -- The rest of the paused round has the same odds in both processes.
    | none =>
      simp only [fastContinuationProcess, continuationProcess, Distribution.expect_map]
      exact fastRemaining_expect rules f (fun t => g (some t))
    -- A full round has the same odds in both processes.
    | some s =>
      simp only [fastContinuationProcess, continuationProcess, Distribution.expect_map]
      exact (fastProcess_sameOdds rules f.order).step s (fun t => g (some t)) ht

/-- Checked answers for a paused Fight: an answer for each result of the paused round, and a
checked row for each state of the witness. -/
structure CertifiedContinuation (rules : RuleSet) (f : FightPhase) where
  witness : CombatWitness
  starts : ∀ e ∈ (fastRemaining rules f.order f.state).entries, witness.contains e.1
  rows : ∀ s ∈ witness.states, witness.RowValid rules f.order s

/-- Why the check of a paused Fight failed. -/
inductive PausedFightFailure where
  /-- One round has more results than the solver's budget allows. -/
  | roundTooLarge
  /-- The solver returned an empty map. It does so only when it stops at a limit of the budget
  (states, round results in memory, work, or round size) or at its pass bound. -/
  | overBudget
  /-- The answers did not pass the check. The Fight can go on forever, for example. -/
  | checkFailed
  deriving DecidableEq, Repr

/-- Names in plain English: "A", "A and B", or "A, B and C". With no names, "no Creatures". -/
def joinNames : List String → String
  | [] => "no Creatures"
  | [a] => a
  | [a, b] => s!"{a} and {b}"
  | a :: rest => s!"{a}, {joinNames rest}"

/-- The message for the author of a live change, which names the living Creatures of the paused
Fight `f` and says why the check failed. A paused Fight keeps its Creatures and the requested
effects stay fixed, so the advice names only what can change: the counter-rules, or the time. -/
def PausedFightFailure.message (e : PausedFightFailure) (f : FightPhase) : String :=
  let fight := s!"The paused Fight against {joinNames (f.state.livingFoes.filterMap fun i =>
    (f.state.foes[i]?).map (·.being.name))}"
  match e with
  | .roundTooLarge => s!"{fight} is too large to check with these rules: the estimated number \
      of results of one round is above the check's limit. Counter-rules that change damage or \
      armor change the size of a round. Revise them, or make the change after the Fight ends."
  | .overBudget => s!"{fight} is over the solver's budget with these rules: checking it needs \
      more states, work or memory than the solver allows. Counter-rules that change damage or \
      armor change the size of the check. Revise them, or make the change after the Fight ends."
  | .checkFailed => s!"{fight} could not be checked: no proof was found that it ends. One \
      possible cause is a stalemate, in which no side can hurt the other under the changed rules. \
      If a counter-rule causes this, revise it."

/-- Check a paused Fight within `budget`, or give the reason why it fails. The rest of the paused
round counts against `budget` as one full round: a limited budget rejects it before it is computed
if it is above the round or batch limit or the work limit. The paused round and the later rounds
use the fast attack. -/
def checkContinuation (rules : RuleSet) (f : FightPhase) (budget : SolveBudget := {}) :
    Except PausedFightFailure (CertifiedContinuation rules f) :=
  let bounds := attackBounds rules f.state
  let paused := roundSizeBound f.order bounds f.state
  if budget.limited && paused > min budget.roundEntries budget.batchEntries then
    .error .roundTooLarge else
  if budget.limited && paused > budget.work then .error .overBudget else
  let starts := (fastRemaining rules f.order f.state).entries.map Prod.fst
  -- The later rounds get the work that the paused round leaves.
  let cache := solveChecked rules f.order bounds starts {budget with work := budget.work - paused}
  let w : CombatWitness := ⟨cache⟩
  if h : w.check rules f.order starts = true then
    .ok ⟨w, fun e he => (CombatWitness.check_sound h).1 e.1 (List.mem_map.mpr ⟨e, he, rfl⟩),
      (CombatWitness.check_sound h).2⟩
  -- The solver returns no answers only when it stops at a budget limit or at its pass bound.
  -- The pass bound is not proved to be enough, so the message can be wrong in that case.
  else if cache.isEmpty then .error .overBudget
  else .error .checkFailed

/-- Check a paused Fight: `checkContinuation` without the reason. -/
def certifyContinuation (rules : RuleSet) (f : FightPhase) : Option (CertifiedContinuation rules f) :=
  (checkContinuation rules f).toOption

/-- The states that the certificate covers: the paused point, and each state of the witness. -/
def CertifiedContinuation.invariant {rules : RuleSet} {f : FightPhase}
    (c : CertifiedContinuation rules f) (s : Option FightState) : Prop :=
  match s with | none => True | some s => c.witness.contains s

/-- A stopping certificate for the paused Fight. Before the paused round, the potential is one
more than the expected rounds left after it. -/
def CertifiedContinuation.stopping {rules : RuleSet} {f : FightPhase}
    (c : CertifiedContinuation rules f) : StoppingCertificate (fastContinuationProcess rules f) c.invariant where
  potential s := match s with
    | none => 1 + (fastRemaining rules f.order f.state).expect (fun s => (c.witness.answer s).rounds)
    | some s => (c.witness.answer s).rounds
  nonnegative s hs := by
    cases s with
    -- Before the paused round: the potential is an expected value of nonnegative numbers.
    | none =>
      have h := (fastRemaining rules f.order f.state).expect_mono
        (fastRemaining_valid rules f.order f.state)
        (fun _ => 0) (fun s => (c.witness.answer s).rounds) (fun e he =>
          (CertifiedFight.stopping ⟨c.witness,c.starts e he,c.rows⟩).nonnegative e.1 (c.starts e he))
      simp only [Distribution.expect_const _ (fastRemaining_valid rules f.order f.state)] at h
      grind
    -- A state of the Fight: the Fight's own certificate gives the bound.
    | some s => exact (CertifiedFight.stopping ⟨c.witness,hs,c.rows⟩).nonnegative s hs
  closed s hs e he := by
    cases s with
    -- Before the paused round: each result of the paused round is a start of the witness.
    | none =>
      simp only [fastContinuationProcess, Functor.map, Distribution.bind, Function.comp_def,
        List.map_cons, List.map_nil] at he
      obtain ⟨t,ht,eq⟩ := List.mem_flatMap.mp he
      have eq := List.mem_singleton.mp eq
      cases eq
      exact c.starts t ht
    -- A state of the Fight: the Fight's own certificate keeps it in the witness.
    | some s =>
      simp only [fastContinuationProcess, Functor.map, Distribution.bind, Function.comp_def,
        List.map_cons, List.map_nil] at he
      obtain ⟨t,ht,eq⟩ := List.mem_flatMap.mp he
      have eq := List.mem_singleton.mp eq
      cases eq
      exact (CertifiedFight.stopping ⟨c.witness,hs,c.rows⟩).closed s hs t ht
  decreases s hs ht := by
    cases s with
    -- Before the paused round: the potential is one more than after it.
    | none => simp [fastContinuationProcess, Distribution.expect_map]
    -- A state of the Fight: the Fight's own certificate gives the decrease.
    | some s =>
      simpa only [fastContinuationProcess, Distribution.expect_map, CertifiedFight.stopping] using
        (CertifiedFight.stopping ⟨c.witness,hs,c.rows⟩).decreases s hs ht

/-- A checked paused Fight ends with probability 1 in the spec process. -/
theorem CertifiedContinuation.ends_almostSurely {rules : RuleSet} {f : FightPhase}
    (c : CertifiedContinuation rules f) : (continuationProcess rules f).AlmostSurelyTerminates none :=
  ((fastContinuation_sameOdds rules f).almostSurely_iff none).mp (c.stopping.almostSure none trivial)

end Rpg.Probability
