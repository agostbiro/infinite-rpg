import Rpg.Probability.CombatCertificate
import Rpg.Game

/-!
An adventure and a character determine one graph. One turn is one scene choice,
including its entire fight. Scene states retain HP; terminal success, death,
and combat-certification failure are distinct. The dice model is independent fair d6,
not a claim that the finite seeded PRNG is an IID source.
-/
namespace Rpg.Probability

/-- Graph states preserve HP after every fight. -/
inductive Node where
  | scene (id : SceneId) (hp : Int)
  | ended
  | dead
  | stalled
  | resuming
  deriving DecidableEq, Repr

/-- A finitely supported rational transition kernel with a distinguished initial state. -/
structure Graph where
  start : Node
  step : Node → Distribution Node

/-- Resolve zero-HP and ending states without spending another player turn. -/
def arrive (a : Adventure) (id : SceneId) (hp : Int) : Node :=
  if hp ≤ 0 then .dead
  else match a.scene? id with
    | none => .stalled
    | some scene => if scene.choices.isEmpty then .ended else .scene id hp

/-- Exact success probability, including untrained skills and automatic failures. -/
def rollProbability (rules : RuleSet) (hero : Being) (target : RollTarget) (modifier : Int) : Rat :=
  match (rules.rollLevel hero target).map (· + modifier) with
  | none => 0
  | some level => if level < rules.minimumRollLevel then 0
      else (dice 3).mass fun roll => (rules.successRoll level roll).succeeded

/-- The edges of a choice are derived from its actual outcome and combat rules. -/
def outcomeEdges (rules : RuleSet) (hero : Being) (a : Adventure) (hp : Int) : Outcome → Distribution Node
  | .goto id => pure (arrive a id hp)
  | .roll target modifier onSuccess onFailure =>
    let p := rollProbability rules hero target modifier
    ⟨[(arrive a onSuccess hp, p), (arrive a onFailure hp, 1 - p)]⟩
  | .fight foes onWin =>
    (checkedCombat rules (turnOrder rules hero foes)
      {hero := {being := hero, hp}, foes := foes.map fun f => {being := f, hp := rules.maxHP f}}).bind fun result => pure (match result with
      | .won remaining => arrive a onWin remaining
      | .died => .dead
      | .stalled => .stalled)

/-- Derive a graph; authors cannot supply independent, invented fight odds. -/
def adventureGraph (rules : RuleSet) (hero : Being) (a : Adventure) : Graph where
  start := arrive a a.start (rules.maxHP hero)
  step node := match node with
    | .dead => pure .dead
    | .ended => pure .ended
    | .stalled => pure .stalled
    | .resuming => pure .stalled
    | .scene id hp => match a.scene? id with
      | none => pure .stalled
      | some scene => if scene.choices.isEmpty then pure .ended
        else ((uniform scene.choices).bind fun choice => outcomeEdges rules hero a hp choice.outcome).collect

/-- State distribution after n scene choices. Death and success are absorbing. -/
def Graph.after (g : Graph) : Nat → Distribution Node
  | 0 => pure g.start
  | n + 1 => ((g.after n).bind g.step).collect

/-- Probability of death by turn n. -/
def Graph.deadBy (g : Graph) (n : Nat) : Rat :=
  (g.after n).mass fun node => decide (node = .dead)

/-- Probability of successful termination by turn n. -/
def Graph.endedBy (g : Graph) (n : Nat) : Rat :=
  (g.after n).mass fun node => decide (node = .ended)

/-- Probability of remaining active in this graph; unverified combat stays stalled. -/
def Graph.activeAt (g : Graph) (n : Nat) : Rat :=
  (g.after n).mass fun node => match node with
    | .scene _ _ | .stalled | .resuming => true
    | _ => false

/-- An exact checkpoint between choices or at the Character's turn in a Fight. -/
inductive ResumePoint where
  | scene (id : SceneId) (hp : Int)
  | fight (phase : FightPhase)

/-- Use the current HP and full paused Fight state. Live admission only accepts Scene or Fight phases. -/
def _root_.Rpg.Game.balancePoint (g : Game) : ResumePoint :=
  match g.phase with
  | .fight f => .fight f
  | _ => .scene (g.sceneId?.getD g.adventure.start) g.hp

/-- Resolve the unfinished round, then the remaining full rounds with exact odds. -/
def remainingCombat (rules : RuleSet) (f : FightPhase) : Distribution CombatResult :=
  let next := (Prod.fst <$> remainingRoundWith (attackDistribution rules) heroPolicy f.order f.state).collect
  (next.bind fun s => checkedCombat rules f.order s).collect

/-- The continuation graph starts at the saved HP and position, including a paused Fight. -/
def continuationGraph (a : AdventureDefinition) (point : ResumePoint) : Graph :=
  let base := adventureGraph a.rules a.hero a.story
  match point with
  | .scene id hp => { base with start := arrive a.story id hp }
  | .fight f =>
    { start := .resuming, step := fun node => match node with
      | .resuming => (remainingCombat a.rules f).bind fun result => pure (match result with
        | .won hp => arrive a.story f.onWin hp
        | .died => .dead
        | .stalled => .stalled)
      | n => base.step n }

end Rpg.Probability
