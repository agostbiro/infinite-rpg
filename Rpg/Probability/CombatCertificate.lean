import Rpg.Probability.CombatProofs
import Rpg.Probability.Stopping

/-! The elimination algorithm is an untrusted certificate producer. This small
checker validates closure, probability equations, and an expected-duration bound
against the shared engine's exact round kernel. No assertion of IID seeded PRNG
output is made: the law here is independent fair dice and `heroPolicy`. -/
namespace Rpg.Probability

def combatProcess (rules : RuleSet) (order : List Actor) : StoppingProcess FightState where
  terminal := FightState.over
  step s := if s.over then pure s else roundDistribution rules heroPolicy order s
  valid s := by
    split
    · exact Distribution.valid_pure _
    · exact roundDistribution_valid rules heroPolicy heroPolicy_valid order s

/-- Only read on a terminal state: death takes precedence, as in the engine. -/
def terminalResult (s : FightState) : CombatResult :=
  if s.hero.alive then .won s.hero.hp else .died

structure CombatWitness where
  entries : CombatCache

def CombatWitness.states (w : CombatWitness) : List FightState := w.entries.map Prod.fst

def CombatWitness.answer (w : CombatWitness) (s : FightState) : CombatAnswer :=
  if s.over then ⟨pure (terminalResult s), 0⟩
  else ((w.entries.find? (fun e => decide (e.1 = s))).map Prod.snd).getD ⟨pure .stalled, 0⟩

def CombatWitness.contains (w : CombatWitness) (s : FightState) : Prop :=
  s.over = true ∨ s ∈ w.states

instance (w : CombatWitness) (s : FightState) : Decidable (w.contains s) := by
  unfold CombatWitness.contains
  infer_instance

def CombatWitness.RowValid (w : CombatWitness) (rules : RuleSet) (order : List Actor) (s : FightState) : Prop :=
  (w.answer s).outcomes.Valid ∧ 0 ≤ (w.answer s).rounds ∧
  (∀ e ∈ ((combatProcess rules order).step s).entries, w.contains e.1) ∧
  (if s.over then True else
    1 + ((combatProcess rules order).step s).expect (fun t => (w.answer t).rounds) ≤ (w.answer s).rounds) ∧
  (w.answer s).outcomes.sameWeights
    (((combatProcess rules order).step s).bind fun t => (w.answer t).outcomes)

def CombatWitness.Accepted (w : CombatWitness) (rules : RuleSet) (order : List Actor) (start : FightState) : Prop :=
  w.contains start ∧ ∀ s ∈ w.states, w.RowValid rules order s

instance (w : CombatWitness) (rules : RuleSet) (order : List Actor) (start : FightState) :
    Decidable (w.Accepted rules order start) := by
  unfold CombatWitness.Accepted CombatWitness.RowValid CombatWitness.contains Distribution.Valid
  infer_instance

/-- Only a successful independent check constructs this record. -/
structure CertifiedFight (rules : RuleSet) (order : List Actor) (start : FightState) where
  witness : CombatWitness
  checked : witness.Accepted rules order start

def certifyFight (rules : RuleSet) (order : List Actor) (start : FightState) :
    Option (CertifiedFight rules order start) :=
  let (_, cache) := (solveCombatAnswer rules heroPolicy order start).run []
  let witness : CombatWitness := ⟨cache⟩
  if h : witness.Accepted rules order start then some ⟨witness,h⟩ else none

variable {rules : RuleSet} {order : List Actor} {start : FightState}

def CertifiedFight.stopping (c : CertifiedFight rules order start) :
    StoppingCertificate (combatProcess rules order) c.witness.contains where
  potential s := (c.witness.answer s).rounds
  nonnegative s hs := by
    rcases hs with ht | hm
    · simp [CombatWitness.answer, ht]
    · exact (c.checked.2 s hm).2.1
  closed s hs e he := by
    rcases hs with ht | hm
    · simp only [combatProcess, ht, ↓reduceIte] at he
      have eq : e.1 = s := by simpa [pure, Pure.pure] using congrArg Prod.fst (List.mem_singleton.mp he)
      rw [eq]
      exact Or.inl ht
    · exact (c.checked.2 s hm).2.2.1 e he
  decreases s hs ht := by
    change s.over = false at ht
    rcases hs with impossible | hm
    · simp [ht] at impossible
    · simpa [ht] using (c.checked.2 s hm).2.2.2.1

/-- A checked fight ends with probability one under the stated ideal policy and dice law. -/
theorem CertifiedFight.ends_almostSurely (c : CertifiedFight rules order start) :
    (combatProcess rules order).AlmostSurelyTerminates start :=
  c.stopping.almostSure start c.checked.1

/-- The same certificate supplies a finite horizon for any requested failure allowance. -/
theorem CertifiedFight.finishes_with_high_probability (c : CertifiedFight rules order start)
    (delta : Rat) (hd : 0 < delta) :
    (combatProcess rules order).unfinished (c.stopping.horizon start delta) start ≤ delta :=
  c.stopping.horizon_sound start c.checked.1 delta hd

def CertifiedFight.outcomes (c : CertifiedFight rules order start) : Distribution CombatResult :=
  (c.witness.answer start).outcomes

theorem CertifiedFight.answer_valid (c : CertifiedFight rules order start)
    (s : FightState) (hs : c.witness.contains s) : (c.witness.answer s).outcomes.Valid := by
  rcases hs with ht | hm
  · simp only [CombatWitness.answer, ht, ↓reduceIte]
    exact Distribution.valid_pure _
  · exact (c.checked.2 s hm).1

theorem CertifiedFight.outcomes_valid (c : CertifiedFight rules order start) : c.outcomes.Valid :=
  c.answer_valid start c.checked.1

def CertifiedFight.outcomeCertificate (c : CertifiedFight rules order start) (event : CombatResult → Bool) :
    OutcomeCertificate (combatProcess rules order) c.witness.contains (fun s => event (terminalResult s)) where
  value s := (c.witness.answer s).outcomes.mass event
  bounded s hs := Distribution.mass_bounds _ (c.answer_valid s hs) event
  closed := c.stopping.closed
  terminalValue s _ ht := by
    change s.over = true at ht
    simp [CombatWitness.answer, ht, Distribution.mass, pure, Pure.pure, Rat.add_zero]
  equation s hs ht := by
    change s.over = false at ht
    rcases hs with impossible | hm
    · simp [ht] at impossible
    · have eq := Distribution.sameWeights_sound _ _ ((c.checked.2 s hm).2.2.2.2)
        (fun result => if event result then 1 else 0)
      simpa only [Distribution.mass_eq_expect, Distribution.expect_bind] using eq

/-- For every outcome event, the certified solver answer is within delta of the
shared engine's finite execution probability at the certificate's explicit horizon. -/
theorem CertifiedFight.outcome_error (c : CertifiedFight rules order start)
    (event : CombatResult → Bool) (delta : Rat) (hd : 0 < delta) :
    let n := c.stopping.horizon start delta
    let exact := (combatProcess rules order).eventBy (fun s => event (terminalResult s)) n start
    exact ≤ c.outcomes.mass event ∧ c.outcomes.mass event ≤ exact + delta :=
  (c.outcomeCertificate event).highProbability_error c.stopping start c.checked.1 delta hd

/-- Public probability calculations expose only checked answers. Failure is explicitly
represented by `stalled`; it does not assert that the actual fight diverges. -/
def checkedCombat (rules : RuleSet) (order : List Actor) (s : FightState) : Distribution CombatResult :=
  match certifyFight rules order s with
  | some c => c.outcomes
  | none => pure .stalled

theorem checkedCombat_valid (rules : RuleSet) (order : List Actor) (s : FightState) :
    (checkedCombat rules order s).Valid := by
  unfold checkedCombat
  split
  · exact CertifiedFight.outcomes_valid _
  · exact Distribution.valid_pure _

end Rpg.Probability
