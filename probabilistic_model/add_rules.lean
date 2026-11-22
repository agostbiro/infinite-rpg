import MarkovRPGAdventureProperties
import MarkovRPGWorkshop

set_option backward.isDefEq.respectTransparency false

/-!+# Typed rule changes and their acceptance obligations

Three different requests are represented explicitly: combat inputs/equipment,
adventure statistics, and adventure topology. They can be combined in one batch.
The proposer may search for compensation; this module never asserts that such
a compensation always exists. Probabilities are exact, with deterministic
acceptance tolerances, not statistical confidence intervals.

Character patches, admission checks and rational certificate checks are
executable. PMF semantics and infinite-horizon assertions are mathematical
objects: we do NOT disguise Classical.decide as an executable validator.
An external generator supplies exact witnesses/proofs, checked by Lean.
-/

namespace MarkovRPG.RuleChanges

open MainRules

/-- Requested player changes. Current HP, identity, resources and running
effects are deliberately preserved; base stats and equipment are edited here. -/
structure CharacterPatch where
  statistics : List (CharacterProperty × Nat) := []
  inventory : Option (List InventoryEntry) := none
  equipment : Option Equipment := none
  deriving Repr, DecidableEq

def CharacterPatch.apply (p : CharacterPatch) (s : CharacterState) : CharacterState :=
  { s with character := { s.character with
      statistics := p.statistics.foldl (fun stats edit => stats.set edit.1 edit.2) s.character.statistics
      inventory := p.inventory.getD s.character.inventory
      equipment := p.equipment.getD s.character.equipment } }

theorem CharacterPatch.preserves_state (p : CharacterPatch) (s : CharacterState) :
    (p.apply s).character.id = s.character.id ∧ (p.apply s).character.name = s.character.name ∧
    (p.apply s).hp = s.hp ∧ (p.apply s).effects = s.effects ∧
    (p.apply s).resources = s.resources := ⟨rfl, rfl, rfl, rfl, rfl⟩

def CharacterPatch.combatAllowed (p : CharacterPatch) (usage : PropertyUsage) : Bool :=
  p.statistics.all (fun e => e.1.isStoredStatistic && usage.combat e.1)

def CharacterPatch.adventureAllowed (p : CharacterPatch) (usage : PropertyUsage) : Bool :=
  p.inventory.isNone && p.equipment.isNone &&
    p.statistics.all (fun e => e.1.isStoredStatistic && usage.adventure e.1)

/-- Overlap triggers recomputation in both domains. No probability preservation
is inferred solely from a usage mask. -/
def CharacterPatch.affectsCombat (p : CharacterPatch) (usage : PropertyUsage) : Bool :=
  p.inventory.isSome || p.equipment.isSome || p.statistics.any (fun e => usage.combat e.1)

def CharacterPatch.affectsAdventure (p : CharacterPatch) (usage : PropertyUsage) : Bool :=
  p.statistics.any (fun e => usage.adventure e.1)

theorem CharacterPatch.shared_recomputes (p : CharacterPatch) (usage : PropertyUsage)
    (key : CharacterProperty) (value : Nat) (hmem : (key, value) ∈ p.statistics)
    (hc : usage.combat key = true) (ha : usage.adventure key = true) :
    p.affectsCombat usage = true ∧ p.affectsAdventure usage = true := by
  have h₁ : p.statistics.any (fun e => usage.combat e.1) = true :=
    List.any_eq_true.mpr ⟨(key, value), hmem, hc⟩
  have h₂ : p.statistics.any (fun e => usage.adventure e.1) = true :=
    List.any_eq_true.mpr ⟨(key, value), hmem, ha⟩
  simp [affectsCombat, affectsAdventure, h₁, h₂]

inductive StructureRequest (V A : Type*) where
  | insertOn (action : A) (destination : V)
  | addOption (source destination : V)
  | removeOption (action : A)
  deriving DecidableEq

/-- Exactly the three requested kinds; a batch is a List of these requests. -/
inductive RuleChange (V A : Type*) where
  | combatChange (patch : CharacterPatch)
  | adventureStatsChange (patch : CharacterPatch)
  | adventureStructureChange (request : StructureRequest V A)

def RuleChange.applyCharacter {V A} : RuleChange V A → CharacterState → CharacterState
  | .combatChange p, s | .adventureStatsChange p, s => p.apply s
  | .adventureStructureChange _, s => s

def RuleChange.allowed {V A} (usage : PropertyUsage) : RuleChange V A → Bool
  | .combatChange p => p.combatAllowed usage
  | .adventureStatsChange p => p.adventureAllowed usage
  | .adventureStructureChange _ => true

def applyBatch {V A} (changes : List (RuleChange V A)) (s : CharacterState) : CharacterState :=
  changes.foldl (fun state change => change.applyCharacter state) s

theorem applyBatch_hp {V A} (changes : List (RuleChange V A)) (s : CharacterState) :
    (applyBatch changes s).hp = s.hp := by
  induction changes generalizing s with
  | nil => rfl
  | cons c cs ih =>
    change (applyBatch cs (c.applyCharacter s)).hp = s.hp
    rw [ih]
    cases c <;> rfl

/-- A snapshot of the live session, independent of any vertex renumbering. -/
structure Session (V : Type*) where
  position : V
  player : CharacterState
  timestamp : Nat
  inCombat : Bool := false

/-- Admission is checked before a proposed compensation is considered. -/
def canChange {V A} (r : Combat.Rules) (usage : PropertyUsage) (s : Session V)
    (changes : List (RuleChange V A)) : Bool :=
  !s.inCombat && decide (0 < s.player.hp) && changes.all (RuleChange.allowed usage) &&
    (applyBatch changes s.player).check r

theorem canChange_sound {V A} (r : Combat.Rules) (usage : PropertyUsage) (s : Session V)
    (changes : List (RuleChange V A)) (h : canChange r usage s changes = true) :
    s.inCombat = false ∧ s.player.alive ∧
    (∀ c ∈ changes, c.allowed usage = true) ∧ (applyBatch changes s.player).WellFormed r := by
  simpa [canChange, CharacterState.alive, Bool.and_eq_true, List.all_eq_true,
    and_assoc] using h

@[simp] theorem cannotChangeDuringCombat {V A} (r : Combat.Rules) (usage : PropertyUsage)
    (s : Session V) (changes : List (RuleChange V A)) (h : s.inCombat = true) :
    canChange r usage s changes = false := by simp [canChange, h]

/-- Enemy compensation is an explicit input. The actual new character and
weapon feed the existing generic combat setup; no cached old kernel is used. -/
def rebuildCombat (r : Combat.Rules) (patch : CharacterPatch)
    (player compensatedEnemy : CharacterState) (first : Combat.Player := .A) :=
  Combat.Setup.fromAdventure r (patch.apply player) compensatedEnemy first

theorem rebuildCombat_inputs (r : Combat.Rules) (patch : CharacterPatch)
    (player enemy : CharacterState) (first : Combat.Player) (c : Combat.Setup r)
    (h : rebuildCombat r patch player enemy first = some c) :
    (c.characters .A).character = (patch.apply player).toCombat ∧
    (c.characters .B).character = enemy.toCombat ∧ c.first = first :=
  Combat.Setup.create_preserves r _ _ first c h

noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal NNReal

/-- An action-indexed view of the existing WorldEvent semantics. Keeping actions
separate is essential: player randomization does not make a pure action random. -/
structure Adventure (r : Combat.Rules) (V A : Type*) where
  initial : V
  player : V → CharacterState
  source : A → V
  event : A → Combat.WorldEvent r V
  terminal : Set V
  defeat : Set V

def eventIsCombat {r : Combat.Rules} {V : Type*} : Combat.WorldEvent r V → Bool
  | .ordinary _ => false
  | .combat _ _ => true

namespace Adventure
variable {r : Combat.Rules} {V A : Type*} [Fintype V] [Fintype A]

def actionsAt (g : Adventure r V A) (s : V) : Finset A :=
  Finset.univ.filter (fun a => g.source a = s)

/-- Uniform testing policy. A missing action becomes a self-loop, and is rejected
by Total below on live states. Terminal states are absorbing by construction. -/
def row (g : Adventure r V A) (s : V) : PMF V :=
  if s ∈ g.terminal then PMF.pure s
  else if h : (g.actionsAt s).Nonempty then
    (PMF.uniformOfFinset (g.actionsAt s) h).bind (fun a => (g.event a).law)
  else PMF.pure s

def chain (g : Adventure r V A) (goal : Set V) : MarkovChain V Unit where
  initial := g.initial
  label _ := none
  transition s v := (g.row s v).toReal
  transition_nonneg _ _ := ENNReal.toReal_nonneg
  transition_sum s := Combat.pmf_sum_toReal (g.row s)
  defeat := goal

def Total (g : Adventure r V A) : Prop :=
  ∀ s, s ∉ g.terminal → (g.actionsAt s).Nonempty

def additional (g : Adventure r V A) (x : ℚ) : Prop :=
  AdventureProperties.EventProperties g.source g.terminal g.event x

/-- Ordinary laws are replaced only in the adventure-statistics case. The scope
certificate below checks that their positive-probability destinations persist. -/
def reweight (g : Adventure r V A) (updates : A → Option (PMF V)) : Adventure r V A :=
  { g with event := fun a => match g.event a, updates a with
      | .ordinary _, some law => .ordinary law
      | old, _ => old }

def SameSupport (g h : Adventure r V A) : Prop :=
  ∀ a v, v ∈ (g.event a).law.support ↔ v ∈ (h.event a).law.support

omit [Fintype V] [Fintype A] in
theorem reweight_combat_unchanged (g : Adventure r V A) (updates : A → Option (PMF V))
    (a : A) (e : Combat.Event r) (next : Combat.FullExit e.setup → V)
    (h : g.event a = .combat e next) : (g.reweight updates).event a = .combat e next := by
  simp [reweight, h]

/-- Pure adventure reweighting preserves the tested topology and the exact
deterministic-action count, provided no support is added or removed. -/
theorem reweight_additional_iff (g : Adventure r V A) (updates : A → Option (PMF V))
    (h : g.SameSupport (g.reweight updates)) (x : ℚ) :
    (g.reweight updates).additional x ↔ g.additional x := by
  have laws : ∀ a, AdventureProperties.outputs ((g.reweight updates).event a).law =
      AdventureProperties.outputs (g.event a).law := by
    intro a
    ext v
    simp only [AdventureProperties.mem_outputs]
    exact (h a v).symm
  have det : ∀ a, AdventureProperties.IsDeterministic ((g.reweight updates).event a).law ↔
      AdventureProperties.IsDeterministic (g.event a).law := by
    intro a
    simp only [AdventureProperties.IsDeterministic, laws]
  have edges : AdventureProperties.decisionEdges Finset.univ g.source
      (fun a => ((g.reweight updates).event a).law) =
      AdventureProperties.decisionEdges Finset.univ g.source (fun a => (g.event a).law) := by
    funext u v
    apply propext
    change (∃ d ∈ Finset.univ, g.source d = u ∧ v ∈ ((g.reweight updates).event d).law.support) ↔ _
    constructor
    · rintro ⟨d, hd, hs, hv⟩
      exact ⟨d, hd, hs, (h d v).mpr hv⟩
    · rintro ⟨d, hd, hs, hv⟩
      exact ⟨d, hd, hs, (h d v).mp hv⟩
  unfold additional AdventureProperties.EventProperties AdventureProperties.HasAdditionalProperties
  change AdventureProperties.NoSmallCycles (AdventureProperties.eventEdges g.terminal
      (AdventureProperties.decisionEdges Finset.univ g.source (fun a => ((g.reweight updates).event a).law))) ∧
      AdventureProperties.HasDeterministicDecisionBound
        (AdventureProperties.liveDecisions g.source g.terminal)
        (fun a => ((g.reweight updates).event a).law) x ↔ _
  simp only [edges, AdventureProperties.HasDeterministicDecisionBound,
    AdventureProperties.deterministicDecisions, det]

/-- A replacement combat carries its own complete exit law and continuation. -/
structure CombatReplacement (r : Combat.Rules) (V : Type*) where
  event : Combat.Event r
  next : Combat.FullExit event.setup → V

def replaceCombats (g : Adventure r V A) (updates : A → Option (CombatReplacement r V)) :
    Adventure r V A :=
  { g with event := fun a => match g.event a, updates a with
      | .combat _ _, some e => .combat e.event e.next
      | old, _ => old }

omit [Fintype V] [Fintype A] in
theorem replaceCombats_ordinary_unchanged (g : Adventure r V A)
    (updates : A → Option (CombatReplacement r V)) (a : A) (law : PMF V)
    (h : g.event a = .ordinary law) : (g.replaceCombats updates).event a = .ordinary law := by
  simp [replaceCombats, h]

omit [Fintype V] [Fintype A] in
theorem replacement_exact (g : Adventure r V A) (updates : A → Option (CombatReplacement r V))
    (a : A) (old : Combat.Event r) (oldNext : Combat.FullExit old.setup → V)
    (replacement : CombatReplacement r V) (h : g.event a = .combat old oldNext)
    (hu : updates a = some replacement) (v : V) :
    (((g.replaceCombats updates).event a).law v).toReal =
      ∑ o, if v = replacement.next o then
        replacement.event.game.exitMass Combat.History.root o.val else 0 := by
  simp only [replaceCombats, h, hu, Combat.WorldEvent.law]
  exact replacement.event.commit_apply replacement.next v

/-- Transport an event, including all collapsed combat exits, to new vertices. -/
def mapEvent {W : Type*} (f : V → W) : Combat.WorldEvent r V → Combat.WorldEvent r W
  | .ordinary law => .ordinary (law.map f)
  | .combat e next => .combat e (f ∘ next)

omit [Fintype V] in
theorem mapEvent_law {W : Type*} (f : V → W) (e : Combat.WorldEvent r V) :
    (mapEvent f e).law = e.law.map f := by
  cases e with
  | ordinary law => rfl
  | combat e next => simp [mapEvent, Combat.WorldEvent.law, Combat.Event.commit, PMF.map_comp]

/-- Insert a fresh event on ONE selected action's route to a destination.
The old direct outcome is rerouted, not kept as a shortcut forming a triangle.
Other actions and other outcomes are preserved. The fresh node has no terminal
label and deterministically continues to the old destination. -/
def insertEvent (g : Adventure r V A) (action : A) (destination : V) :
    Adventure r (Sum V Unit) (Sum A Unit) where
  initial := .inl g.initial
  player := Sum.elim g.player (fun _ => g.player destination)
  source := Sum.elim (fun a => .inl (g.source a)) (fun _ => .inr ())
  event := Sum.elim
    (fun a => mapEvent (fun v => if a = action ∧ v = destination then .inr () else .inl v)
      (g.event a))
    (fun _ => .ordinary (PMF.pure (.inl destination)))
  terminal := {v | ∃ old ∈ g.terminal, v = .inl old}
  defeat := {v | ∃ old ∈ g.defeat, v = .inl old}

omit [Fintype V] [Fintype A] in
theorem insertEvent_preserves_other (g : Adventure r V A) (action : A) (destination : V)
    (other : A) (h : other ≠ action) :
    ((g.insertEvent action destination).event (.inl other)).law =
      (g.event other).law.map Sum.inl := by
  simp only [insertEvent, Sum.elim_inl, mapEvent_law]
  simp [h]

omit [Fintype V] [Fintype A] in
@[simp] theorem insertEvent_continuation (g : Adventure r V A) (action : A) (destination : V) :
    ((g.insertEvent action destination).event (.inr ())).law = PMF.pure (.inl destination) := rfl

omit [Fintype V] [Fintype A] in
theorem insertEvent_fresh (g : Adventure r V A) (action : A) (destination : V) :
    (Sum.inr () : Sum V Unit) ∉ (g.insertEvent action destination).terminal := by
  simp [insertEvent]

/-- Adding an option creates a distinct action, even if another action happens
to have the same outcome law. Uniform choice is recomputed by `row`. -/
def addOption (g : Adventure r V A) (source : V) (event : Combat.WorldEvent r V) :
    Adventure r V (Sum A Unit) where
  initial := g.initial
  player := g.player
  source := Sum.elim g.source (fun _ => source)
  event := Sum.elim g.event (fun _ => event)
  terminal := g.terminal
  defeat := g.defeat

/-- Removing the last live option is allowed as a proposal, but cannot obtain
the Total proof required for acceptance. No fallback action is silently added. -/
def removeOption (g : Adventure r V A) (action : A) :
    Adventure r V {a : A // a ≠ action} where
  initial := g.initial
  player := g.player
  source a := g.source a.val
  event a := g.event a.val
  terminal := g.terminal
  defeat := g.defeat

omit [Fintype V] [Fintype A] in
theorem removeOption_preserves (g : Adventure r V A) (action other : A) (h : other ≠ action) :
    (g.removeOption action).event ⟨other, h⟩ = g.event other := rfl

end Adventure

/-- One fixed difficulty contract. Rebalancing cannot replace the reference law
or widen its tolerance. Combat bands are independent from adventure loss bands. -/
structure Requirements where
  duration : ProbabilityMeasure (WithTop Nat)
  durationTolerance : ℝ≥0
  lossLower : ℝ
  lossUpper : ℝ
  combatLower : ℝ
  combatUpper : ℝ
  deterministicMax : ℚ

/-- Entire remaining CDF against the reference at the ORIGINAL timestamp. -/
def ResumedFair {V Label : Type*} [Fintype V] (M : MarkovChain V Label) (s : V)
    (D : ProbabilityMeasure (WithTop Nat)) (t : Nat) (ε : ℝ≥0) : Prop :=
  ∃ ht : DefeatTime.cdf D t < 1, ∀ n, |M.h n s - DefeatTime.risk D t n ht| ≤ (ε : ℝ)

theorem resumedFair_at_zero {V Label : Type*} [Fintype V] (M : MarkovChain V Label)
    (s : V) (D : ProbabilityMeasure (WithTop Nat)) (ε : ℝ≥0)
    (hzero : DefeatTime.cdf D 0 = 0) :
    ResumedFair M s D 0 ε ↔ M.IsMarkovFairDistrib s D ε := by
  simp [ResumedFair, MarkovChain.IsMarkovFairDistrib, DefeatTime.risk, hzero]

/-- The two-event condition is a consequence, not a duplicated acceptance test. -/
theorem ResumedFair.twoStep {V Label : Type*} [Fintype V] {M : MarkovChain V Label}
    {s : V} {D : ProbabilityMeasure (WithTop Nat)} {t : Nat} {ε : ℝ≥0}
    (h : ResumedFair M s D t ε) :
    ∃ ht, M.IsMarkovTwoStepBalancedDistrib s D t ht ε := by
  obtain ⟨ht, hf⟩ := h
  exact ⟨ht, (M.isMarkovTwoStepBalancedDistrib_iff_abs s D t ht ε).mpr (hf 2)⟩

/-- Canonical inventory after combat, retaining all surviving item mechanics
and exact quantities. Spent stacks are absent rather than resurrected. -/
def exitInventory {r : Combat.Rules} {setup : Combat.Setup r} (o : Combat.FullExit setup) :
    List CombatInventoryEntry :=
  (List.finRange r.itemSlots).filterMap fun i =>
    if (o.character .A).stock i = 0 then none
    else ((o.character .A).items i).map (fun item => ⟨item, ((o.character .A).stock i).val⟩)

/-- Outstanding timed effects survive into the next adventure snapshot with
their remaining duration. Their ordering in that snapshot is immaterial. -/
def exitEffects {r : Combat.Rules} {setup : Combat.Setup r} (o : Combat.FullExit setup) :
    List ActiveEffect :=
  (Finset.univ : Finset (Combat.EffectKey r)).toList.filterMap fun key =>
    if h : 0 < ((o.character .A).remaining key).val then
      ((o.character .A).modifiers key).map
        (fun modifier => ⟨modifier, ⟨((o.character .A).remaining key).val, h⟩⟩)
    else none

/-- Matching a complete combat exit is stronger than matching only Win/Lose or
mean HP. The next fight reinitializes effect sources from this adventure snapshot;
within a fight the existing source/refresh semantics are unchanged. -/
def MatchesExit {r : Combat.Rules} {setup : Combat.Setup r}
    (state : CharacterState) (o : Combat.FullExit setup) : Prop :=
  state.character.id = (o.character .A).id ∧
  state.hp = ((o.character .A).hp.val : Int) ∧
  state.character.statistics = (o.character .A).statistics ∧
  state.character.equipment = (o.character .A).equipment ∧
  state.resources = (o.character .A).resources ∧
  state.character.combatInventory = exitInventory o ∧ state.effects.Perm (exitEffects o)

def Adventure.ValidFrom {r : Combat.Rules} {V A : Type*} [Fintype V] [Fintype A]
    (g : Adventure r V A) (s : V) (t : Nat) (c : Requirements) : Prop :=
  g.Total ∧ g.defeat ⊆ g.terminal ∧ s ∉ g.terminal ∧
  (∀ v, (g.player v).WellFormed r) ∧
  (∀ a, g.source a ∈ g.terminal → (g.event a).law = PMF.pure (g.source a)) ∧
  g.additional c.deterministicMax ∧
  (g.chain g.terminal).hInf s = 1 ∧
  (g.chain g.defeat).IsMarkovpqFair s c.lossUpper c.lossLower ∧
  ResumedFair (g.chain g.terminal) s c.duration t c.durationTolerance ∧
  (∀ a, match g.event a with
    | .ordinary _ => True
    | .combat e next => e.IsFair c.combatUpper c.combatLower ∧
        e.game = Combat.Game.uniform e.setup ∧
        (e.setup.characters .A).character = (g.player (g.source a)).toCombat ∧
        ∀ o, MatchesExit (g.player (next o)) o ∧
          (next o ∈ g.defeat ↔ o.outcome = .Lose))

/-- Admission and commitment are distinct. A candidate is not installed until
its graph, changes and frozen difficulty contract have been proved consistent. -/
structure Candidate {r : Combat.Rules} {V A W B : Type*}
    (old : Adventure r V A) (session : Session V) (changes : List (RuleChange V A)) where
  graph : Adventure r W B
  current : W

/-- Observable graph structure for matching structural requests. -/
def Adventure.hasEdge {r : Combat.Rules} {V A : Type*} (g : Adventure r V A) (s v : V) : Prop :=
  ∃ a, g.source a = s ∧ v ∈ (g.event a).law.support

/-- Scope is a proof obligation, not a license to replace the game arbitrarily.
Old vertex identities embed into the new graph. Pure statistic changes preserve
the set of actions; ordinary-only reweighting preserves all outcome supports.
Shared statistics may require both combat and ordinary events to be rebuilt. -/
structure Scope {r : Combat.Rules} {V A W B : Type*}
    (old : Adventure r V A) (new : Adventure r W B)
    (usage : PropertyUsage) (changes : List (RuleChange V A)) where
  vertex : V ↪ W
  action : A → Option B
  distinctActions : ∀ a a' b, action a = some b → action a' = some b → a = a'
  source : ∀ a b, action a = some b → new.source b = vertex (old.source a)
  labels : ∀ v, (vertex v ∈ new.terminal ↔ v ∈ old.terminal) ∧
    (vertex v ∈ new.defeat ↔ v ∈ old.defeat)
  initial : new.initial = vertex old.initial
  player : ∀ v, new.player (vertex v) = applyBatch changes (old.player v)
  noStructure : (∀ request, RuleChange.adventureStructureChange request ∉ changes) →
    Function.Bijective vertex ∧ ∃ correspondence : A ≃ B,
      ∀ a, action a = some (correspondence a)
  eventKinds : (∀ request, RuleChange.adventureStructureChange request ∉ changes) →
    ∀ a b, action a = some b → eventIsCombat (new.event b) = eventIsCombat (old.event a)
  ordinaryUnchanged :
    (∀ p, RuleChange.adventureStatsChange p ∉ changes) →
    (∀ p, RuleChange.combatChange p ∈ changes → p.affectsAdventure usage = false) →
    (∀ request, RuleChange.adventureStructureChange request ∉ changes) →
    ∀ a b law, action a = some b → old.event a = .ordinary law →
      new.event b = .ordinary (law.map vertex)
  combatUnchanged :
    (∀ p, RuleChange.combatChange p ∉ changes) →
    (∀ p, RuleChange.adventureStatsChange p ∈ changes → p.affectsCombat usage = false) →
    (∀ request, RuleChange.adventureStructureChange request ∉ changes) →
    ∀ a b e next, action a = some b → old.event a = .combat e next →
      new.event b = .combat e (vertex ∘ next)
  reweightSupport :
    (∀ p, RuleChange.combatChange p ∉ changes) →
    (∀ p, RuleChange.adventureStatsChange p ∈ changes → p.affectsCombat usage = false) →
    (∀ request, RuleChange.adventureStructureChange request ∉ changes) →
    ∀ a b v, action a = some b →
      (v ∈ (old.event a).law.support ↔ vertex v ∈ (new.event b).law.support)
  insertions : ∀ a v, RuleChange.adventureStructureChange (.insertOn a v) ∈ changes →
    v ∈ (old.event a).law.support ∧ ∃ b fresh, action a = some b ∧ fresh ∉ Set.range vertex ∧
      fresh ∈ (new.event b).law.support ∧
      vertex v ∉ (new.event b).law.support ∧ new.hasEdge fresh (vertex v)
  additions : ∀ s v, RuleChange.adventureStructureChange (.addOption s v) ∈ changes →
    ∃ b, (∀ a, action a ≠ some b) ∧ new.source b = vertex s ∧
      vertex v ∈ (new.event b).law.support
  removals : ∀ a, RuleChange.adventureStructureChange (.removeOption a) ∈ changes →
    action a = none

/-- Concrete consistency obligations: requested hero, time and input HP are
not replaced by a fresh start or undone during enemy compensation. -/
structure Certificate {r : Combat.Rules} {V A W B : Type*}
    [Fintype W] [Fintype B] (old : Adventure r V A) (session : Session V)
    (changes : List (RuleChange V A)) (usage : PropertyUsage) (contract : Requirements)
    (candidate : Candidate (W := W) (B := B) old session changes) : Prop where
  admitted : canChange r usage session changes = true
  oldPlayer : old.player session.position = session.player
  position : ∃ scope : Scope old candidate.graph usage changes,
    candidate.current = scope.vertex session.position
  valid : candidate.graph.ValidFrom candidate.current session.timestamp contract

/-- Player preservation follows from the graph's stored states and the scope
mapping; there is no second independently editable player copy in a candidate. -/
theorem Certificate.currentPlayer {r : Combat.Rules} {V A W B : Type*}
    [Fintype W] [Fintype B] {old : Adventure r V A} {session : Session V}
    {changes : List (RuleChange V A)} {usage : PropertyUsage} {contract : Requirements}
    {candidate : Candidate (W := W) (B := B) old session changes}
    (cert : Certificate old session changes usage contract candidate) :
    candidate.graph.player candidate.current = applyBatch changes session.player := by
  obtain ⟨scope, position⟩ := cert.position
  rw [position, scope.player, cert.oldPlayer]

/-- A committed session uses the certified replacement graph and keeps the
absolute clock. There is no unchecked fall-through branch. -/
def commit {r : Combat.Rules} {V A W B : Type*} [Fintype W] [Fintype B]
    {old : Adventure r V A} {session : Session V} {changes : List (RuleChange V A)}
    {usage : PropertyUsage} {contract : Requirements}
    (candidate : Candidate (W := W) (B := B) old session changes)
    (_certificate : Certificate old session changes usage contract candidate) : Session W :=
  ⟨candidate.current, candidate.graph.player candidate.current, session.timestamp, false⟩

theorem commit_preserves {r : Combat.Rules} {V A W B : Type*} [Fintype W] [Fintype B]
    {old : Adventure r V A} {session : Session V} {changes : List (RuleChange V A)}
    {usage : PropertyUsage} {contract : Requirements}
    (candidate : Candidate (W := W) (B := B) old session changes)
    (cert : Certificate old session changes usage contract candidate) :
    (commit candidate cert).timestamp = session.timestamp ∧
    (commit candidate cert).player = applyBatch changes session.player ∧
    (commit candidate cert).player.hp = session.player.hp ∧
    candidate.graph.ValidFrom (commit candidate cert).position
      (commit candidate cert).timestamp contract := by
  exact ⟨rfl, cert.currentPlayer, by rw [show (commit candidate cert).player = _ from cert.currentPlayer,
    applyBatch_hp], cert.valid⟩

/-! Exact finite certificates for the entire remaining duration curve. A finite
prefix alone is insufficient: the tail bounds below prove all later times too.
This permits cycles; no finite bound on actual play length is assumed. -/

theorem curve_band_of_prefix_tail (f g : Nat → ℝ) (N : Nat) (ε : ℝ)
    (hf : Monotone f) (hg : Monotone g) (uf : ∀ n, f n ≤ 1) (ug : ∀ n, g n ≤ 1)
    (prefixBand : ∀ n, n ≤ N → |f n - g n| ≤ ε)
    (tailF : 1 - ε ≤ f N) (tailG : 1 - ε ≤ g N) :
    ∀ n, |f n - g n| ≤ ε := by
  intro n
  by_cases h : n ≤ N
  · exact prefixBand n h
  · have hfn := hf (show N ≤ n by omega)
    have hgn := hg (show N ≤ n by omega)
    have ufn := uf n
    have ugn := ug n
    rw [abs_le]
    constructor <;> linarith

theorem resumedFair_of_prefix_tail {V Label : Type*} [Fintype V]
    (M : MarkovChain V Label) (s : V) (D : ProbabilityMeasure (WithTop Nat))
    (t N : Nat) (ht : DefeatTime.cdf D t < 1) (ε : ℝ≥0)
    (prefixBand : ∀ n, n ≤ N → |M.h n s - DefeatTime.risk D t n ht| ≤ (ε : ℝ))
    (tailM : 1 - (ε : ℝ) ≤ M.h N s)
    (tailD : 1 - (ε : ℝ) ≤ DefeatTime.risk D t N ht) : ResumedFair M s D t ε := by
  refine ⟨ht, curve_band_of_prefix_tail _ _ N ε (M.h_mono s) ?_
    (fun n => M.h_le_one n s) (fun n => DefeatTime.risk_le_one D t n ht) prefixBand tailM tailD⟩
  intro a b hab
  unfold DefeatTime.risk
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (DefeatTime.cdf_mono D (Nat.add_le_add_left hab t)) _)
    (by linarith)

end

/-- Executable exact-rational checks on a proposed finite CDF certificate.
`reference k` is the original CDF at t+k, and `elapsed` is its value at t.
The reference must come from the FROZEN original contract, not a fitted candidate. -/
def resumeCheck {N : Nat} (actual reference : Fin (N + 1) → ℚ) (elapsed ε : ℚ) : Bool :=
  decide (0 ≤ ε) && decide (elapsed < 1) &&
    (List.finRange (N + 1)).all (fun k =>
      decide (|actual k - (reference k - elapsed) / (1 - elapsed)| ≤ ε)) &&
    decide (1 - ε ≤ actual ⟨N, by omega⟩) &&
    decide (1 - ε ≤ (reference ⟨N, by omega⟩ - elapsed) / (1 - elapsed))

theorem resumeCheck_spec {N : Nat} (actual reference : Fin (N + 1) → ℚ) (elapsed ε : ℚ) :
    resumeCheck actual reference elapsed ε = true ↔
      0 ≤ ε ∧ elapsed < 1 ∧
      (∀ k, |actual k - (reference k - elapsed) / (1 - elapsed)| ≤ ε) ∧
      1 - ε ≤ actual ⟨N, by omega⟩ ∧
      1 - ε ≤ (reference ⟨N, by omega⟩ - elapsed) / (1 - elapsed) := by
  simp [resumeCheck, Bool.and_eq_true, List.all_eq_true, and_assoc]

noncomputable section
open MeasureTheory
open scoped NNReal

/-- A generator's Boolean numeric check implies the FULL remaining duration
property, using the existing kernel-checked dynamic-programming tables.
Termination of the reference is proved by positive paths; cyclic references
are allowed. The two tail inequalities justify the unbounded quantifier. -/
theorem resumeCheck_sound {n m N t : Nat}
    (g : Workshop.Graph n) (reference : Workshop.Graph m)
    (paths : Workshop.Paths reference) (s : Fin n)
    (a : Workshop.Horizon g g.terminal N)
    (b : Workshop.Horizon reference reference.terminal (t + N))
    (ε : ℝ≥0) (q : ℚ) (hq : (q : ℝ) = (ε : ℝ))
    (checked : resumeCheck (fun k => a.table k s)
      (fun k => b.table ⟨t + k.val, Nat.add_lt_add_left k.isLt t⟩ reference.initial)
      (b.table ⟨t, Nat.lt_succ_of_le (Nat.le_add_right t N)⟩ reference.initial) q = true) :
    ResumedFair (g.chain g.terminal) s
      (ReferenceLaw.PhaseType.law
        ⟨reference.chain reference.terminal, paths.terminates reference reference.initial⟩)
      t ε := by
  let D : ReferenceLaw.PhaseType (Fin m) Unit :=
    ⟨reference.chain reference.terminal, paths.terminates reference reference.initial⟩
  have refAt (k : Fin (N + 1)) : DefeatTime.cdf D.law (t + k.val) =
      (b.table ⟨t + k.val, Nat.add_lt_add_left k.isLt t⟩ reference.initial : ℝ) := by
    exact (ReferenceLaw.PhaseType.cdf_law D (t + k.val)).trans
      (b.correct reference reference.terminal (t + N)
        ⟨t + k.val, Nat.add_lt_add_left k.isLt t⟩ reference.initial)
  have refZero : DefeatTime.cdf D.law t =
      (b.table ⟨t, Nat.lt_succ_of_le (Nat.le_add_right t N)⟩ reference.initial : ℝ) := by
    simpa using refAt ⟨0, Nat.zero_lt_succ N⟩
  obtain ⟨_, he, prefixBand, tailA, tailB⟩ := (resumeCheck_spec _ _ _ _).mp checked
  have ht : DefeatTime.cdf D.law t < 1 := by
    rw [refZero]
    exact_mod_cast he
  apply resumedFair_of_prefix_tail (g.chain g.terminal) s D.law t N ht ε
  · intro k hk
    rw [a.correct g g.terminal N ⟨k, Nat.lt_succ_of_le hk⟩ s]
    unfold DefeatTime.risk
    rw [refAt ⟨k, Nat.lt_succ_of_le hk⟩, refZero, ← hq]
    exact_mod_cast prefixBand ⟨k, Nat.lt_succ_of_le hk⟩
  · rw [a.correct g g.terminal N ⟨N, Nat.lt_succ_self N⟩ s, ← hq]
    exact_mod_cast tailA
  · unfold DefeatTime.risk
    rw [refAt ⟨N, Nat.lt_succ_self N⟩, refZero, ← hq]
    exact_mod_cast tailB

end
end MarkovRPG.RuleChanges
