import Rpg.Probability.Balance

/-! Bounded game trajectories use the same combat rules as play. Unresolved
outcomes are retained so validation cannot discard unfavorable samples. -/
namespace Rpg.Probability.Simulation

/-- A timeout records the first turn whose outcome is unknown. -/
inductive Finish where
  | dead | ended | censored | invalid
  deriving Repr, BEq

/-- A completed outcome, or the first unresolved turn. -/
structure Trace where
  finish : Finish
  turn : Nat
  deriving Repr, BEq

/-- Choose uniformly under the ideal uniform-word assumption, up to modulo bias.
As with the engine's d6, the finite PRNG is not proved IID. -/
def choose (n : Nat) : Roll Nat := do
  if n ≤ 1 then return 0
  let (word, next) := (← get).next
  set next
  return word.toNat % n

/-- The simulator's Player, with seeded random choices: each maneuver with chance 1/3, then a
living target with equal chances if the maneuver attacks. This is `heroPolicy` in the model. -/
def pickManeuver (s : FightState) : Roll (Maneuver × Nat) := do
  let m := maneuverMenu.getD (← choose maneuverMenu.length) .attack
  if !m.attacks then return (m, 0)
  let living := s.livingFoes
  return (m, living.getD (← choose living.length) 0)

/-- A Fight of at most `fuel` rounds, with the same rounds as play (`roundWith`). The Player
uses `pick`. A Fight that does not end in time gives `none`, which is not a win or a loss. -/
def fight (rules : RuleSet) (pick : FightState → Roll (Maneuver × Nat)) (order : List Actor) :
    Nat → FightState → Roll (Option FightState)
  | fuel, state => do
    if state.over then return some state
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      let (next, _) ← roundWith (attack rules) pick order state
      fight rules pick order fuel next

/-- One trajectory; scene choices, not combat rounds, advance its turn count. -/
def trajectory (a : AdventureDefinition) (roundLimit : Nat) :
    Nat → SceneId → Int → Nat → Roll Trace
  | fuel, id, hp, turns => do
    if hp ≤ 0 then return ⟨.dead, turns⟩
    let some scene := a.story.scene? id | return ⟨.invalid, turns⟩
    if scene.choices.isEmpty then return ⟨.ended, turns⟩
    match fuel with
    | 0 => return ⟨.censored, turns + 1⟩
    | fuel + 1 =>
      let some choice := scene.choices[← choose scene.choices.length]?
        | return ⟨.invalid, turns⟩
      match choice.outcome with
      | .goto next => trajectory a roundLimit fuel next hp (turns + 1)
      | .roll target modifier yes no =>
        let level := (a.rules.rollLevel a.hero target).map (· + modifier)
        let (result, _) ← makeRoll a.rules a.hero.name target modifier level
        trajectory a roundLimit fuel (if result.succeeded then yes else no) hp (turns + 1)
      | .fight foes next =>
        let state : FightState :=
          { hero := { being := a.hero, hp }, foes := foes.map fun foe => { being := foe, hp := a.rules.maxHP foe } }
        let result ← fight a.rules pickManeuver (turnOrder a.rules a.hero foes) roundLimit state
        match result with
        | none => return ⟨.censored, turns + 1⟩
        | some state =>
          if !state.hero.alive then return ⟨.dead, turns + 1⟩
          trajectory a roundLimit fuel next state.hero.hp (turns + 1)

/-- Resume at the Character's turn; already completed enemy turns and wounds stay completed. -/
def resumeFight (rules : RuleSet) (f : FightPhase) (roundLimit : Nat) : Roll (Option FightState) := do
  if roundLimit = 0 then return none
  let (next, _) ← remainingRoundWith (attack rules) pickManeuver f.order f.state
  fight rules pickManeuver f.order (roundLimit - 1) next

/-- Sample a continuation from the same checkpoint used by `continuationGraph`. -/
def fromPoint (a : AdventureDefinition) (roundLimit fuel : Nat) (point : ResumePoint) : Roll Trace := do
  match point with
  | .scene id hp => trajectory a roundLimit fuel id hp 0
  | .fight f =>
    if fuel = 0 then return ⟨.censored, 1⟩
    match ← resumeFight a.rules f roundLimit with
    | none => return ⟨.censored, 1⟩
    | some s =>
      if !s.hero.alive then return ⟨.dead, 1⟩
      trajectory a roundLimit (fuel - 1) f.onWin s.hero.hp 1

end Rpg.Probability.Simulation
