import Rpg.Probability.CombatCertificate
import Rpg.Spec

/-! Combat evidence for an Adventure. Each distinct Fight is checked at every entry HP, with one
witness for all entry HPs. The solver that makes the witness is not trusted. This file also gives
the exit law of each Fight at each entry HP (`CertifiedAdventureCombat.exitLaw`). -/
namespace Rpg.Probability

def fightStart (rules : RuleSet) (hero : Being) (hp : Int) (foes : List Being) : FightState :=
  {hero := {being := hero, hp}, foes := foes.map fun f => {being := f, hp := rules.maxHP f}}

def encounterFoes (a : Adventure) : List (List Being) :=
  (a.scenes.flatMap fun sc => sc.choices.filterMap fun ch => match ch.outcome with
    | .fight foes _ => some foes
    | _ => none).eraseDups

/-- Zero HP is included as an already terminal state. -/
def entryHPs (rules : RuleSet) (hero : Being) : List Nat := List.range (rules.maxHP hero + 1)

structure CertifiedEncounter (rules : RuleSet) (hero : Being) (foes : List Being) where
  witness : CombatWitness
  starts : ∀ hp ∈ entryHPs rules hero, witness.contains (fightStart rules hero hp foes)
  rows : ∀ s ∈ witness.states, witness.RowValid rules (turnOrder rules hero foes) s

/-- The start state of the Fight against `foes` at each entry HP. -/
def encounterStarts (rules : RuleSet) (hero : Being) (foes : List Being) : List FightState :=
  (entryHPs rules hero).map fun (hp : Nat) => fightStart rules hero hp foes

def certifyEncounter (rules : RuleSet) (hero : Being) (foes : List Being) :
    Option (CertifiedEncounter rules hero foes) :=
  let order := turnOrder rules hero foes
  let starts := encounterStarts rules hero foes
  let witness : CombatWitness :=
    ⟨solveFight (fastRound rules order) starts (roundSizeEstimate rules order)⟩
  if h : witness.check rules order starts = true then
    some ⟨witness,
      fun hp hm => (CombatWitness.check_sound h).1 _ (List.mem_map.mpr ⟨hp, hm, rfl⟩),
      (CombatWitness.check_sound h).2⟩
  else none

def CertifiedEncounter.atHP {rules : RuleSet} {hero : Being} {foes : List Being}
    (c : CertifiedEncounter rules hero foes) (hp : Int) (lo : 0 ≤ hp)
    (hi : hp ≤ rules.maxHP hero) : CertifiedFight rules (turnOrder rules hero foes)
      (fightStart rules hero hp foes) := by
  refine ⟨c.witness, ?_, c.rows⟩
  have hm : hp.toNat ∈ entryHPs rules hero := by simp [entryHPs]; omega
  have h := c.starts hp.toNat hm
  simpa [Int.toNat_of_nonneg lo] using h

private def certifyEncounters (rules : RuleSet) (hero : Being) :
    (fs : List (List Being)) → Option ((foes : List Being) → foes ∈ fs → CertifiedEncounter rules hero foes)
  | [] => some (fun _ h => False.elim (List.not_mem_nil h))
  | f :: fs => do
    let first ← certifyEncounter rules hero f
    let rest ← certifyEncounters rules hero fs
    return fun foes h => if eq : foes = f then eq ▸ first else
      rest foes ((List.mem_cons.mp h).resolve_left eq)

/-- Every story encounter has checked termination and outcome evidence for all entry HPs. -/
structure CertifiedAdventureCombat (a : AdventureDefinition) where
  encounter : (foes : List Being) → foes ∈ encounterFoes a.story → CertifiedEncounter a.rules a.hero foes

def certifyAdventureCombat (a : AdventureDefinition) : Option (CertifiedAdventureCombat a) :=
  (certifyEncounters a.rules a.hero (encounterFoes a.story)).map CertifiedAdventureCombat.mk

theorem CertifiedAdventureCombat.ends_almostSurely {a : AdventureDefinition}
    (c : CertifiedAdventureCombat a) (foes : List Being) (hf : foes ∈ encounterFoes a.story)
    (hp : Int) (lo : 0 ≤ hp) (hi : hp ≤ a.rules.maxHP a.hero) :
    (combatProcess a.rules (turnOrder a.rules a.hero foes)).AlmostSurelyTerminates
      (fightStart a.rules a.hero hp foes) :=
  ((c.encounter foes hf).atHP hp lo hi).ends_almostSurely

theorem CertifiedAdventureCombat.finishes_with_high_probability {a : AdventureDefinition}
    (c : CertifiedAdventureCombat a) (foes : List Being) (hf : foes ∈ encounterFoes a.story)
    (hp : Int) (lo : 0 ≤ hp) (hi : hp ≤ a.rules.maxHP a.hero) (delta : Rat) (hd : 0 < delta) :
    ∃ n, (combatProcess a.rules (turnOrder a.rules a.hero foes)).unfinished n
      (fightStart a.rules a.hero hp foes) ≤ delta :=
  c.ends_almostSurely foes hf hp lo hi delta hd

/-! ## Exit laws

The exit law of a Fight is the chance of each result (a win with each HP left, or death) for one
entry HP. An exact model of the whole Adventure can use it in place of the Fight. -/

/-- The exit law of the Fight against `foes` when the Character enters it with `hp` HP. Only
the entry HPs from 0 to full HP are checked, so `hp` must be at most full HP. -/
def CertifiedEncounter.exitLaw {rules : RuleSet} {hero : Being} {foes : List Being}
    (c : CertifiedEncounter rules hero foes) (hp : Nat)
    -- The entry HP is at most full HP.
    (hi : hp ≤ rules.maxHP hero) : Distribution CombatResult :=
  (c.atHP hp (by omega) (by omega)).outcomes

/-- The exit law at `hp`, or `none` if `hp` is more than full HP and so was not checked. -/
def CertifiedEncounter.exitLaw? {rules : RuleSet} {hero : Being} {foes : List Being}
    (c : CertifiedEncounter rules hero foes) (hp : Nat) : Option (Distribution CombatResult) :=
  if hi : hp ≤ rules.maxHP hero then some (c.exitLaw hp hi) else none

/-- The exit law is the exact law of the Fight. For each set of results and each `n`, its chance
is between the chance to end in the set within `n` rounds and that chance plus the chance that
the Fight is not over after `n` rounds, which goes to zero. -/
theorem CertifiedEncounter.exitLaw_exact {rules : RuleSet} {hero : Being} {foes : List Being}
    (c : CertifiedEncounter rules hero foes) (hp : Nat)
    -- The entry HP is at most full HP.
    (hi : hp ≤ rules.maxHP hero)
    (event : CombatResult → Bool) (n : Nat) :
    let p := combatProcess rules (turnOrder rules hero foes)
    let start := fightStart rules hero hp foes
    -- The chance to end with the event within `n` rounds is at most the exit law's chance.
    p.eventBy (fun s => event (terminalResult s)) n start ≤ (c.exitLaw hp hi).mass event ∧
    -- The exit law's chance is at most that chance plus the chance to be unfinished.
    (c.exitLaw hp hi).mass event ≤
      p.eventBy (fun s => event (terminalResult s)) n start + p.unfinished n start := by
  intro p start
  let f := c.atHP hp (by omega) (by omega)
  have h := (f.outcomeCertificate event).finite_error n start f.checked.1
  have same := fastProcess_sameOdds rules (turnOrder rules hero foes)
  rw [same.eventBy_eq, same.unfinished_eq] at h
  exact h

/-- The exit law is a probability distribution. -/
theorem CertifiedEncounter.exitLaw_valid {rules : RuleSet} {hero : Being} {foes : List Being}
    (c : CertifiedEncounter rules hero foes) (hp : Nat) (hi : hp ≤ rules.maxHP hero) :
    (c.exitLaw hp hi).Valid :=
  CertifiedFight.outcomes_valid _

/-- The exit law gives no weight to `stalled`: every Fight ends in a win or a death. -/
theorem CertifiedEncounter.exitLaw_stalled {rules : RuleSet} {hero : Being} {foes : List Being}
    (c : CertifiedEncounter rules hero foes) (hp : Nat) (hi : hp ≤ rules.maxHP hero) :
    (c.exitLaw hp hi).mass (· == .stalled) = 0 := by
  let p := combatProcess rules (turnOrder rules hero foes)
  let start := fightStart rules hero hp foes
  -- No end state has the result `stalled`, so its chance within `n` rounds is zero.
  have never : ∀ n s, p.eventBy (fun s => terminalResult s == .stalled) n s = 0 := by
    have hz : ∀ s, (terminalResult s == .stalled) = false := by
      intro s
      unfold terminalResult
      split <;> rfl
    intro n
    induction n with
    -- With no rounds, only an end state counts, and its result is not `stalled`.
    | zero =>
      intro s
      simp [StoppingProcess.eventBy, hz]
    -- With one more round, the chance is the round's expected value of zero.
    | succ n ih =>
      intro s
      simp only [StoppingProcess.eventBy]
      split
      -- The Fight is over at `s`.
      · simp [hz]
      -- The Fight goes on from `s`.
      · have zero : p.eventBy (fun s => terminalResult s == .stalled) n = fun _ => 0 := funext ih
        rw [zero]
        exact Distribution.expect_const _ (p.valid _) 0
  have lower := Distribution.mass_bounds _ (c.exitLaw_valid hp hi) (· == .stalled)
  -- The chance is at most every positive number, so it is zero.
  have upper : ∀ delta : Rat, 0 < delta → (c.exitLaw hp hi).mass (· == .stalled) ≤ delta := by
    intro delta hd
    let f := c.atHP hp (by omega) (by omega)
    have h := (c.exitLaw_exact hp hi (· == .stalled) (f.stopping.horizon start delta)).2
    have tail := f.finishes_with_high_probability delta hd
    rw [never, Rat.zero_add] at h
    exact Rat.le_trans h tail
  have hle : (c.exitLaw hp hi).mass (· == .stalled) ≤ 0 := by
    apply Classical.byContradiction
    intro hn
    have pos : 0 < (c.exitLaw hp hi).mass (· == .stalled) := Rat.not_le.mp hn
    have half := upper ((c.exitLaw hp hi).mass (· == .stalled) / 2) (by grind)
    grind
  exact Rat.le_antisymm hle lower.1

/-- The exit law of a story Fight in a certified Adventure, at entry HP `hp`. -/
def CertifiedAdventureCombat.exitLaw {a : AdventureDefinition} (c : CertifiedAdventureCombat a)
    (foes : List Being) (hf : foes ∈ encounterFoes a.story) (hp : Nat)
    -- The entry HP is at most full HP.
    (hi : hp ≤ a.rules.maxHP a.hero) : Distribution CombatResult :=
  (c.encounter foes hf).exitLaw hp hi

end Rpg.Probability
