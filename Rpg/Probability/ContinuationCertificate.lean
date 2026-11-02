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

structure CertifiedContinuation (rules : RuleSet) (f : FightPhase) where
  witness : CombatWitness
  starts : ∀ e ∈ (remainingDistribution rules f).entries, witness.contains e.1
  rows : ∀ s ∈ witness.states, witness.RowValid rules f.order s

def certifyContinuation (rules : RuleSet) (f : FightPhase) : Option (CertifiedContinuation rules f) :=
  let cache := (remainingDistribution rules f).entries.foldl (fun cache e =>
    ((solveCombatAnswer rules heroPolicy f.order e.1).run cache).2) []
  let w : CombatWitness := ⟨cache⟩
  have : Decidable ((∀ e ∈ (remainingDistribution rules f).entries, w.contains e.1) ∧
      ∀ s ∈ w.states, w.RowValid rules f.order s) := by
    unfold CombatWitness.RowValid CombatWitness.contains Distribution.Valid
    infer_instance
  if h : (∀ e ∈ (remainingDistribution rules f).entries, w.contains e.1) ∧
      ∀ s ∈ w.states, w.RowValid rules f.order s then some ⟨w,h.1,h.2⟩ else none

def CertifiedContinuation.invariant {rules : RuleSet} {f : FightPhase}
    (c : CertifiedContinuation rules f) (s : Option FightState) : Prop :=
  match s with | none => True | some s => c.witness.contains s

def CertifiedContinuation.stopping {rules : RuleSet} {f : FightPhase}
    (c : CertifiedContinuation rules f) : StoppingCertificate (continuationProcess rules f) c.invariant where
  potential s := match s with
    | none => 1 + (remainingDistribution rules f).expect (fun s => (c.witness.answer s).rounds)
    | some s => (c.witness.answer s).rounds
  nonnegative s hs := by
    cases s with
    | none =>
      have h := (remainingDistribution rules f).expect_mono (remainingDistribution_valid rules f)
        (fun _ => 0) (fun s => (c.witness.answer s).rounds) (fun e he =>
          (CertifiedFight.stopping ⟨c.witness,c.starts e he,c.rows⟩).nonnegative e.1 (c.starts e he))
      simp only [Distribution.expect_const _ (remainingDistribution_valid rules f)] at h
      grind
    | some s => exact (CertifiedFight.stopping ⟨c.witness,hs,c.rows⟩).nonnegative s hs
  closed s hs e he := by
    cases s with
    | none =>
      simp only [continuationProcess, Functor.map, Distribution.bind, Function.comp_def,
        List.map_cons, List.map_nil] at he
      obtain ⟨t,ht,eq⟩ := List.mem_flatMap.mp he
      have eq := List.mem_singleton.mp eq
      cases eq
      exact c.starts t ht
    | some s =>
      simp only [continuationProcess, Functor.map, Distribution.bind, Function.comp_def,
        List.map_cons, List.map_nil] at he
      obtain ⟨t,ht,eq⟩ := List.mem_flatMap.mp he
      have eq := List.mem_singleton.mp eq
      cases eq
      exact (CertifiedFight.stopping ⟨c.witness,hs,c.rows⟩).closed s hs t ht
  decreases s hs ht := by
    cases s with
    | none => simp [continuationProcess, Distribution.expect_map]
    | some s =>
      simpa only [continuationProcess, Distribution.expect_map, CertifiedFight.stopping] using
        (CertifiedFight.stopping ⟨c.witness,hs,c.rows⟩).decreases s hs ht

theorem CertifiedContinuation.ends_almostSurely {rules : RuleSet} {f : FightPhase}
    (c : CertifiedContinuation rules f) : (continuationProcess rules f).AlmostSurelyTerminates none :=
  c.stopping.almostSure none trivial

end Rpg.Probability
