import MarkovRPGCombatExits

/-!
# Combat as one adventure event

An accepted combat has live inputs and a proved almost-sure exit. Its full exit
law is used as a single adventure transition; internal actions do not count as
adventure events. Combat fairness and whole-adventure fairness remain separate.

No agreement between a supplied summary and the combat is assumed: the event
law is constructed from the combat itself. Adventure continuations receive the
complete exit, including remaining HP, stocks and effects. If a later strategy
needs internal combat history beyond this state, that memory must be exported
as well; forgetting such memory is not asserted to preserve its behavior.
-/

noncomputable section
open Classical
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

namespace MarkovRPG.Combat

variable {r : Rules}

/-- Termination is a real obligation: finite state space alone does not imply it. -/
structure Event (r : Rules) where
  setup : Setup r
  game : Game setup
  alive : setup.initial.output = none
  terminates : game.hInf none History.root = 1

def Event.resolve (e : Event r) : PMF (FullExit e.setup) :=
  e.game.resolve History.root e.terminates

/-- An exact acceptance band, reusing the existing combat property. -/
def Event.IsFair (e : Event r) (p q : ℝ) : Prop := e.game.IsValid p q

theorem Event.fair_iff (e : Event r) (p q : ℝ) :
    e.IsFair p q ↔ q ≤ (e.resolve.map FullExit.outcome .Lose).toReal ∧
      (e.resolve.map FullExit.outcome .Lose).toReal ≤ p := by
  rw [Event.IsFair, Game.IsValid]
  have hm := e.game.resolve_outcome History.root e.terminates .Lose
  change (e.resolve.map FullExit.outcome .Lose).toReal = _ at hm
  rw [hm]
  simp only [e.alive, e.terminates, true_and]
  exact and_comm

/-- The adventure may route, award loot, or choose a new scene using the complete
combat result. All internal paths have already been summed by `resolve`. -/
def Event.then (e : Event r) {State : Type*}
    (continuation : FullExit e.setup → PMF State) : PMF State :=
  e.resolve.bind continuation

theorem Event.then_apply (e : Event r) {State : Type*}
    (continuation : FullExit e.setup → PMF State) (next : State) :
    (e.then continuation next).toReal =
      ∑ o, e.game.exitMass History.root o.val * (continuation o next).toReal := by
  rw [Event.then, pmf_bind_toReal]
  simp only [Event.resolve, Game.resolve_apply]

/-- A deterministic continuation sums exactly the exits in the destination fiber. -/
def Event.commit (e : Event r) {State : Type*}
    (next : FullExit e.setup → State) : PMF State := e.resolve.map next

theorem Event.commit_apply (e : Event r) {State : Type*}
    (next : FullExit e.setup → State) (v : State) :
    (e.commit next v).toReal =
      ∑ o, if v = next o then e.game.exitMass History.root o.val else 0 := by
  rw [Event.commit, pmf_map_toReal]
  simp only [Event.resolve, Game.resolve_apply]

/-- Collapsing combat commutes with every subsequent continuation that observes
its full output. This is the generic composition proof, independent of an adventure. -/
theorem Event.composition (e : Event r) {State Next : Type*}
    (afterCombat : FullExit e.setup → PMF State) (future : State → PMF Next) :
    (e.then afterCombat).bind future =
      e.resolve.bind (fun o => (afterCombat o).bind future) :=
  PMF.bind_bind _ _ _

/-- Canonical return state: scene/world updates cannot accidentally overwrite
the resolved participants. Presentation and other NPCs may live in `World`. -/
structure AdventureReturn (r : Rules) (Scene World : Type*) where
  scene : Scene
  participants : Player → CharacterResult r
  world : World

def Event.returnToAdventure (e : Event r) {Scene World : Type*}
    (scene : FullExit e.setup → Scene) (world : FullExit e.setup → World) :
    PMF (AdventureReturn r Scene World) :=
  e.commit (fun o => ⟨scene o, o.character, world o⟩)

/-- Every possible returned world contains the exact resolved character data. -/
theorem Event.returnToAdventure_preserves (e : Event r) {Scene World : Type*}
    (scene : FullExit e.setup → Scene) (world : FullExit e.setup → World)
    (next : AdventureReturn r Scene World)
    (hnext : next ∈ (e.returnToAdventure scene world).support) :
    ∃ o ∈ e.resolve.support, next.scene = scene o ∧ next.world = world o ∧
      ∀ p, (next.participants p).id = (e.setup.characters p).character.id ∧
        (next.participants p).hp = o.val.hp p ∧
        (next.participants p).stock = o.val.stock p ∧
        (next.participants p).remaining = o.val.remaining p := by
  rw [returnToAdventure, commit, PMF.mem_support_map_iff] at hnext
  obtain ⟨o, ho, rfl⟩ := hnext
  exact ⟨o, ho, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The same exact combat graph probabilities are inherited by the adventure. -/
theorem Event.stationary_outcome (e : Event r) (policy : Policy e.setup)
    (rep : e.game.Represents policy) (outcome : Outcome) :
    (e.resolve.map FullExit.outcome outcome).toReal =
      (e.setup.chain policy (some outcome)).hInf e.setup.initial :=
  Game.Represents.resolve_outcome rep e.terminates outcome

/-- Random entry states are integrated over their entire distribution. In
particular, random HP is not replaced by mean HP before resolving combat. -/
def mixEvents {Input State : Type*} (inputs : PMF Input) (event : Input → Event r)
    (continuation : (x : Input) → FullExit (event x).setup → PMF State) : PMF State :=
  inputs.bind (fun x => (event x).then (continuation x))

theorem mixEvents_apply {Input State : Type*} [Fintype Input]
    (inputs : PMF Input) (event : Input → Event r)
    (continuation : (x : Input) → FullExit (event x).setup → PMF State) (v : State) :
    (mixEvents inputs event continuation v).toReal =
      ∑ x, (inputs x).toReal *
        ∑ o, (event x).game.exitMass History.root o.val * (continuation x o v).toReal := by
  rw [mixEvents, pmf_bind_toReal]
  simp only [Event.then_apply]

/-- Typed adventure nodes select ordinary transitions or a complete combat event. -/
inductive WorldEvent (r : Rules) (State : Type*) where
  | ordinary (law : PMF State)
  | combat (event : Event r) (next : FullExit event.setup → State)

def WorldEvent.law {State : Type*} : WorldEvent r State → PMF State
  | .ordinary law => law
  | .combat event next => event.commit next

/-- One transition is one adventure event, regardless of combat duration. The
result is a stochastic matrix by PMF normalization, without extra hypotheses. -/
def eventChain {State Label : Type*} [Fintype State]
    (initial : State) (label : State → Option Label) (defeat : Set State)
    (events : State → WorldEvent r State) : MarkovChain State Label where
  initial := initial
  label := label
  defeat := defeat
  transition s next := ((events s).law next).toReal
  transition_nonneg _ _ := ENNReal.toReal_nonneg
  transition_sum s := pmf_sum_toReal (events s).law

theorem eventChain_combat_row {State Label : Type*} [Fintype State]
    (initial : State) (label : State → Option Label) (defeat : Set State)
    (events : State → WorldEvent r State) (s : State) (event : Event r)
    (next : FullExit event.setup → State) (hs : events s = .combat event next) (v : State) :
    (eventChain initial label defeat events).transition s v =
      ∑ o, if v = next o then event.game.exitMass History.root o.val else 0 := by
  change ((events s).law v).toReal = _
  rw [hs]
  exact event.commit_apply next v

end MarkovRPG.Combat
