import Rpg.Probability.Graph

/-! Probability claims require a normalized kernel. The generated graph satisfies
that requirement because every combat answer crosses the certificate checker. -/
namespace Rpg.Probability

def Graph.Valid (g : Graph) : Prop := ∀ node, (g.step node).Valid

def Graph.Absorbing (g : Graph) : Prop :=
  g.step .dead = pure .dead ∧ g.step .ended = pure .ended ∧ g.step .stalled = pure .stalled

theorem rollProbability_bounds (rules : RuleSet) (hero : Being) (target : RollTarget) (modifier : Int) :
    0 ≤ rollProbability rules hero target modifier ∧ rollProbability rules hero target modifier ≤ 1 := by
  unfold rollProbability
  split
  · decide +kernel
  · split
    · decide +kernel
    · exact Distribution.mass_bounds _ (dice_valid 3) _

theorem outcomeEdges_valid (rules : RuleSet) (hero : Being) (a : Adventure) (hp : Int) (o : Outcome) :
    (outcomeEdges rules hero a hp o).Valid := by
  cases o with
  | goto id => exact Distribution.valid_pure _
  | roll target modifier yes no =>
    have hb := rollProbability_bounds rules hero target modifier
    constructor
    · simp only [outcomeEdges, List.mem_cons, List.not_mem_nil, or_false]
      intro e he
      rcases he with rfl | rfl <;> simp only <;> grind
    · simp [outcomeEdges, Rat.add_zero]; grind
  | fight foes win =>
    exact Distribution.valid_bind _ _ (checkedCombat_valid _ _ _) (fun _ => Distribution.valid_pure _)

theorem adventureGraph_valid (rules : RuleSet) (hero : Being) (a : Adventure) :
    (adventureGraph rules hero a).Valid := by
  intro node
  cases node <;> try exact Distribution.valid_pure _
  simp only [adventureGraph]
  split
  · exact Distribution.valid_pure _
  · split
    · exact Distribution.valid_pure _
    · next scene h =>
      apply Distribution.valid_collect
      apply Distribution.valid_bind
      · apply uniform_valid
        simpa only [List.isEmpty_iff] using h
      · intro choice
        exact outcomeEdges_valid _ _ _ _ _

theorem adventureGraph_absorbing (rules : RuleSet) (hero : Being) (a : Adventure) :
    (adventureGraph rules hero a).Absorbing := ⟨rfl,rfl,rfl⟩

theorem remainingCombat_valid (rules : RuleSet) (f : FightPhase) : (remainingCombat rules f).Valid := by
  apply Distribution.valid_collect
  apply Distribution.valid_bind
  · exact Distribution.valid_collect _ (Distribution.valid_map _ _ (remainingRound_valid _ _ _))
  · exact checkedCombat_valid rules f.order

theorem continuationGraph_valid (a : AdventureDefinition) (point : ResumePoint) :
    (continuationGraph a point).Valid := by
  cases point with
  | scene id hp => exact adventureGraph_valid _ _ _
  | fight f =>
    intro node
    cases node <;> simp only [continuationGraph]
    all_goals first
      | exact adventureGraph_valid a.rules a.hero a.story _
      | exact Distribution.valid_bind _ _ (remainingCombat_valid _ _) (fun _ => Distribution.valid_pure _)

theorem continuationGraph_absorbing (a : AdventureDefinition) (point : ResumePoint) :
    (continuationGraph a point).Absorbing := by
  cases point <;> exact ⟨rfl,rfl,rfl⟩

theorem Graph.after_valid (g : Graph) (h : g.Valid) (n : Nat) : (g.after n).Valid := by
  induction n with
  | zero => exact Distribution.valid_pure _
  | succ n ih => exact Distribution.valid_collect _ (Distribution.valid_bind _ _ ih h)

theorem Graph.deadBy_bounds (g : Graph) (h : g.Valid) (n : Nat) :
    0 ≤ g.deadBy n ∧ g.deadBy n ≤ 1 :=
  Distribution.mass_bounds _ (g.after_valid h n) _

theorem Graph.endedBy_bounds (g : Graph) (h : g.Valid) (n : Nat) :
    0 ≤ g.endedBy n ∧ g.endedBy n ≤ 1 :=
  Distribution.mass_bounds _ (g.after_valid h n) _

theorem Graph.activeAt_bounds (g : Graph) (h : g.Valid) (n : Nat) :
    0 ≤ g.activeAt n ∧ g.activeAt n ≤ 1 :=
  Distribution.mass_bounds _ (g.after_valid h n) _

/-- The terminal and active events partition every normalized state law. -/
theorem Graph.probability_partition (g : Graph) (valid : g.Valid) (n : Nat) :
    g.deadBy n + g.endedBy n + g.activeAt n = 1 := by
  unfold Graph.deadBy Graph.endedBy Graph.activeAt
  simp only [Distribution.mass_eq_expect, Distribution.expect]
  rw [← weightedSum_add, ← weightedSum_add]
  calc
    _ = weightedSum (g.after n).entries (fun _ => 1) := by
      congr 1
      funext x
      cases x <;> simp <;> decide +kernel
    _ = 1 := Distribution.expect_const _ (g.after_valid valid n) 1

/-- Mass at an absorbing node cannot decrease in a normalized graph. -/
theorem Graph.absorbing_mass_mono (g : Graph) (h : g.Valid) (target : Node)
    (absorbing : g.step target = pure target) (n : Nat) :
    (g.after n).mass (fun x => decide (x = target)) ≤
      (g.after (n+1)).mass (fun x => decide (x = target)) := by
  simp only [Graph.after, Distribution.mass_eq_expect, Distribution.expect_collect, Distribution.expect_bind]
  apply Distribution.expect_mono _ (g.after_valid h n)
  intro e _
  by_cases eq : e.1 = target
  · simp [eq, absorbing, Distribution.expect_pure]
  · simp only [eq, decide_false, Bool.false_eq_true, ↓reduceIte]
    simpa only [Distribution.mass_eq_expect] using
      (Distribution.mass_bounds _ (h e.1) (fun x => decide (x = target))).1

theorem Graph.deadBy_mono (g : Graph) (h : g.Valid) (absorbing : g.Absorbing) (n : Nat) :
    g.deadBy n ≤ g.deadBy (n+1) := g.absorbing_mass_mono h .dead absorbing.1 n

theorem Graph.endedBy_mono (g : Graph) (h : g.Valid) (absorbing : g.Absorbing) (n : Nat) :
    g.endedBy n ≤ g.endedBy (n+1) := g.absorbing_mass_mono h .ended absorbing.2.1 n

end Rpg.Probability
