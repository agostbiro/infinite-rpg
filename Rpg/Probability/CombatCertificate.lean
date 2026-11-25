import Rpg.Probability.FastCombat
import Rpg.Probability.Stopping
import Std.Data.HashMap.Lemmas

/-!
# Combat certificates

The solver is not trusted. It gives an answer for each state of a Fight. This checker checks
the answers against the exact odds of one round: each result of a round has an answer, each
answer is the round followed by the answers of its results, and the expected number of rounds
left goes down by one each round. The dice are fair and independent, and the Player is
`heroPolicy`. This says nothing about the seeded dice of play.

The theorems are about `combatProcess`, whose step is `roundDistribution`. The checker uses
`fastProcess`, whose step is `fastRound`. The two have the same odds (`fastProcess_sameOdds`),
so each fact that the checker proves for `fastProcess` also holds for `combatProcess`. -/
namespace Rpg.Probability

/-- The spec Fight as a random process: each step is one round of `roundDistribution` with
`heroPolicy`. A Fight that is over stays as it is. -/
def combatProcess (rules : RuleSet) (order : List Actor) : StoppingProcess FightState where
  terminal := FightState.over
  step s := if s.over then pure s else roundDistribution rules heroPolicy order s
  valid s := by
    split
    · exact Distribution.valid_pure _
    · exact roundDistribution_valid rules heroPolicy heroPolicy_valid order s

/-- The process that the checker uses: `combatProcess` with `fastRound` in place of
`roundDistribution`. -/
def fastProcess (rules : RuleSet) (order : List Actor) : StoppingProcess FightState where
  terminal := FightState.over
  step := fastStep rules order
  valid := fastStep_valid rules order

/-- The fast process has the odds of `combatProcess`. -/
theorem fastProcess_sameOdds (rules : RuleSet) (order : List Actor) :
    (fastProcess rules order).SameOdds (combatProcess rules order) where
  terminal := rfl
  step s f ht := by
    change s.over = false at ht
    simp only [fastProcess, combatProcess, fastStep, ht, Bool.false_eq_true, ↓reduceIte]
    exact fastRound_expect rules order s f

/-- Only read on a terminal state: death takes precedence, as in the engine. -/
def terminalResult (s : FightState) : CombatResult :=
  if s.hero.alive then .won s.hero.hp else .died

/-- The solved states and their candidate answers. -/
structure CombatWitness where
  entries : CombatCache

/-- The states that the witness has an answer for. -/
def CombatWitness.states (w : CombatWitness) : List FightState := w.entries.keys

/-- The answer of the witness for `s`. An ended Fight has its own result. A state with no
answer gets `stalled`. -/
def CombatWitness.answer (w : CombatWitness) (s : FightState) : CombatAnswer :=
  if s.over then ⟨pure (terminalResult s), 0⟩
  else w.entries.getD s ⟨pure .stalled, 0⟩

/-- The witness covers `s`: the Fight is over at `s`, or the witness has an answer for `s`. -/
def CombatWitness.contains (w : CombatWitness) (s : FightState) : Prop :=
  s.over = true ∨ w.entries.contains s = true

instance (w : CombatWitness) (s : FightState) : Decidable (w.contains s) := by
  unfold CombatWitness.contains
  infer_instance

/-- A state the witness covers and that is not over is one of its states. -/
theorem CombatWitness.mem_states {w : CombatWitness} {s : FightState} (h : w.contains s)
    (ongoing : s.over = false) : s ∈ w.states := by
  rcases h with done | hm
  -- An ended state contradicts `ongoing`.
  · simp [done] at ongoing
  -- A state in the map is one of its keys.
  · exact Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_contains.mpr hm)

/-- The checks on the row of `s`: its answer is a probability law, its round budget is not
negative, each result of its round is covered, the budget drops by at least one round in
expectation, and the answer is the round followed by the answers of its results. -/
def CombatWitness.RowValid (w : CombatWitness) (rules : RuleSet) (order : List Actor) (s : FightState) : Prop :=
  (w.answer s).outcomes.Valid ∧ 0 ≤ (w.answer s).rounds ∧
  (∀ e ∈ ((fastProcess rules order).step s).entries, w.contains e.1) ∧
  (if s.over then True else
    1 + ((fastProcess rules order).step s).expect (fun t => (w.answer t).rounds) ≤ (w.answer s).rounds) ∧
  (w.answer s).outcomes.sameWeights
    (((fastProcess rules order).step s).bind fun t => (w.answer t).outcomes)

/-- The witness covers `start`, and each of its rows is valid. -/
def CombatWitness.Accepted (w : CombatWitness) (rules : RuleSet) (order : List Actor) (start : FightState) : Prop :=
  w.contains start ∧ ∀ s ∈ w.states, w.RowValid rules order s

instance (w : CombatWitness) (rules : RuleSet) (order : List Actor) (start : FightState) :
    Decidable (w.Accepted rules order start) := by
  unfold CombatWitness.Accepted CombatWitness.RowValid CombatWitness.contains Distribution.Valid
  infer_instance

/-- `RowValid` as one Bool test. It computes the round once and uses it in each check. -/
def CombatWitness.rowCheck (w : CombatWitness) (rules : RuleSet) (order : List Actor)
    (s : FightState) : Bool :=
  let a := w.answer s
  let d := (fastProcess rules order).step s
  a.outcomes.entries.all (fun e => decide (0 ≤ e.2)) &&
  decide ((a.outcomes.entries.map Prod.snd).sum = 1) &&
  decide (0 ≤ a.rounds) &&
  d.entries.all (fun e => decide (w.contains e.1)) &&
  (s.over || decide (1 + d.expect (fun t => (w.answer t).rounds) ≤ a.rounds)) &&
  decide (a.outcomes.sameWeights (d.bind fun t => (w.answer t).outcomes))

/-- A row that passes `rowCheck` is valid. -/
theorem CombatWitness.rowCheck_sound {w : CombatWitness} {rules : RuleSet} {order : List Actor}
    {s : FightState} (h : w.rowCheck rules order s = true) : w.RowValid rules order s := by
  simp only [CombatWitness.rowCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨nonneg, total⟩, rounds⟩, closed⟩, drift⟩, same⟩ := h
  refine ⟨⟨nonneg, total⟩, rounds, closed, ?_, same⟩
  split
  -- An ended Fight has no budget check.
  · trivial
  -- A Fight that goes on passed the budget check.
  · next ongoing => simpa [ongoing] using drift

/-- Check that the witness covers each state of `starts` and that every row is valid. The rows
are checked on many cores. -/
def CombatWitness.check (w : CombatWitness) (rules : RuleSet) (order : List Actor)
    (starts : List FightState) : Bool :=
  starts.all (fun s => decide (w.contains s)) && parallelAll (w.rowCheck rules order) w.states

/-- A witness that passes `check` covers each start and has only valid rows. -/
theorem CombatWitness.check_sound {w : CombatWitness} {rules : RuleSet} {order : List Actor}
    {starts : List FightState} (h : w.check rules order starts = true) :
    (∀ s ∈ starts, w.contains s) ∧ ∀ s ∈ w.states, w.RowValid rules order s := by
  simp only [CombatWitness.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun s hs => CombatWitness.rowCheck_sound (parallelAll_sound h.2 s hs)⟩

/-- Only a successful independent check constructs this record. -/
structure CertifiedFight (rules : RuleSet) (order : List Actor) (start : FightState) where
  witness : CombatWitness
  checked : witness.Accepted rules order start

/-- Solve the Fight from `start` within `budget` and check the answers. It is `none` if the check
fails, also when the Fight is over the budget. -/
def certifyFight (rules : RuleSet) (order : List Actor) (start : FightState)
    (budget : SolveBudget := {}) : Option (CertifiedFight rules order start) :=
  let witness : CombatWitness :=
    ⟨solveChecked rules order (attackBounds rules start) [start] budget⟩
  if h : witness.check rules order [start] = true then
    some ⟨witness, (CombatWitness.check_sound h).1 start (by simp), (CombatWitness.check_sound h).2⟩
  else none

variable {rules : RuleSet} {order : List Actor} {start : FightState}

/-- The checked answers give a stopping certificate for `fastProcess`. The potential of a state
is its expected number of rounds left. -/
def CertifiedFight.stopping (c : CertifiedFight rules order start) :
    StoppingCertificate (fastProcess rules order) c.witness.contains where
  potential s := (c.witness.answer s).rounds
  nonnegative s hs := by
    by_cases ht : s.over
    -- An ended state has no rounds left.
    · simp [CombatWitness.answer, ht]
    -- A live state has a checked row with a nonnegative budget.
    · exact (c.checked.2 s (CombatWitness.mem_states hs (by simpa using ht))).2.1
  closed s hs e he := by
    rcases hs with ht | hm
    -- An ended state steps only to itself.
    · simp only [fastProcess, fastStep, ht, ↓reduceIte] at he
      have eq : e.1 = s := by simpa [pure, Pure.pure] using congrArg Prod.fst (List.mem_singleton.mp he)
      rw [eq]
      exact Or.inl ht
    -- A state of the witness.
    · by_cases ht : s.over
      -- If it is over, it steps only to itself.
      · simp only [fastProcess, fastStep, ht, ↓reduceIte] at he
        have eq : e.1 = s := by simpa [pure, Pure.pure] using congrArg Prod.fst (List.mem_singleton.mp he)
        rw [eq]
        exact Or.inl ht
      -- If it is live, its checked row covers each result of its round.
      · exact (c.checked.2 s (CombatWitness.mem_states (Or.inr hm) (by simpa using ht))).2.2.1 e he
  decreases s hs ht := by
    change s.over = false at ht
    simpa [ht] using (c.checked.2 s (CombatWitness.mem_states hs ht)).2.2.2.1

/-- A checked fight ends with probability one under the stated ideal policy and dice law. -/
theorem CertifiedFight.ends_almostSurely (c : CertifiedFight rules order start) :
    (combatProcess rules order).AlmostSurelyTerminates start :=
  ((fastProcess_sameOdds rules order).almostSurely_iff start).mp
    (c.stopping.almostSure start c.checked.1)

/-- The same certificate supplies a finite horizon for any requested failure allowance. -/
theorem CertifiedFight.finishes_with_high_probability (c : CertifiedFight rules order start)
    (delta : Rat) (hd : 0 < delta) :
    (combatProcess rules order).unfinished (c.stopping.horizon start delta) start ≤ delta := by
  rw [← (fastProcess_sameOdds rules order).unfinished_eq]
  exact c.stopping.horizon_sound start c.checked.1 delta hd

/-- The checked exit law of the Fight from `start`. -/
def CertifiedFight.outcomes (c : CertifiedFight rules order start) : Distribution CombatResult :=
  (c.witness.answer start).outcomes

theorem CertifiedFight.answer_valid (c : CertifiedFight rules order start)
    (s : FightState) (hs : c.witness.contains s) : (c.witness.answer s).outcomes.Valid := by
  by_cases ht : s.over
  · simp only [CombatWitness.answer, ht, ↓reduceIte]
    exact Distribution.valid_pure _
  · exact (c.checked.2 s (CombatWitness.mem_states hs (by simpa using ht))).1

theorem CertifiedFight.outcomes_valid (c : CertifiedFight rules order start) : c.outcomes.Valid :=
  c.answer_valid start c.checked.1

def CertifiedFight.outcomeCertificate (c : CertifiedFight rules order start) (event : CombatResult → Bool) :
    OutcomeCertificate (fastProcess rules order) c.witness.contains (fun s => event (terminalResult s)) where
  value s := (c.witness.answer s).outcomes.mass event
  bounded s hs := Distribution.mass_bounds _ (c.answer_valid s hs) event
  closed := c.stopping.closed
  terminalValue s _ ht := by
    change s.over = true at ht
    simp [CombatWitness.answer, ht, Distribution.mass, pure, Pure.pure, Rat.add_zero]
  equation s hs ht := by
    change s.over = false at ht
    have eq := Distribution.sameWeights_sound _ _
      ((c.checked.2 s (CombatWitness.mem_states hs ht)).2.2.2.2)
      (fun result => if event result then 1 else 0)
    simpa only [Distribution.mass_eq_expect, Distribution.expect_bind] using eq

/-- For every outcome event, the certified solver answer is within delta of the
shared engine's finite execution probability at the certificate's explicit horizon. -/
theorem CertifiedFight.outcome_error (c : CertifiedFight rules order start)
    (event : CombatResult → Bool) (delta : Rat) (hd : 0 < delta) :
    let n := c.stopping.horizon start delta
    let exact := (combatProcess rules order).eventBy (fun s => event (terminalResult s)) n start
    exact ≤ c.outcomes.mass event ∧ c.outcomes.mass event ≤ exact + delta := by
  intro n exact
  have h := (c.outcomeCertificate event).highProbability_error c.stopping start c.checked.1 delta hd
  simp only [exact, ← (fastProcess_sameOdds rules order).eventBy_eq]
  exact h

/-- The checked outcomes of a Fight, or `stalled` if the check fails. The solver has no budget
here, so the size of a Fight does not change these odds. The balance theorems are about them. -/
def checkedCombat (rules : RuleSet) (order : List Actor) (s : FightState) : Distribution CombatResult :=
  match certifyFight rules order s SolveBudget.unlimited with
  | some c => c.outcomes
  | none => pure .stalled

theorem checkedCombat_valid (rules : RuleSet) (order : List Actor) (s : FightState) :
    (checkedCombat rules order s).Valid := by
  unfold checkedCombat
  split
  · exact CertifiedFight.outcomes_valid _
  · exact Distribution.valid_pure _

end Rpg.Probability
