import Rpg.Probability.CombatCertificate
import Rpg.Spec

/-! Mandatory combat evidence for an adventure. Each distinct encounter is checked
at every possible entry HP, sharing the producer's cache across those starts.
The expensive producer is outside the trusted proof boundary. -/
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

def certifyEncounter (rules : RuleSet) (hero : Being) (foes : List Being) :
    Option (CertifiedEncounter rules hero foes) :=
  let cache := ((entryHPs rules hero).reverse.foldl (fun cache (hp : Nat) =>
    ((solveCombatAnswer rules heroPolicy (turnOrder rules hero foes)
      (fightStart rules hero hp foes)).run cache).2) [])
  let witness : CombatWitness := ⟨cache⟩
  have : Decidable ((∀ hp ∈ entryHPs rules hero, witness.contains (fightStart rules hero hp foes)) ∧
      (∀ s ∈ witness.states, witness.RowValid rules (turnOrder rules hero foes) s)) := by
    unfold CombatWitness.RowValid CombatWitness.contains Distribution.Valid
    infer_instance
  if h : (∀ hp ∈ entryHPs rules hero, witness.contains (fightStart rules hero hp foes)) ∧
      (∀ s ∈ witness.states, witness.RowValid rules (turnOrder rules hero foes) s) then
    some ⟨witness,h.1,h.2⟩
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

end Rpg.Probability
