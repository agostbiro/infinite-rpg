import Rpg.Probability.Fairness

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

/-- Bounded combat uses the same rounds as play; timeout is not a loss or win. -/
def fight (rules : RuleSet) (order : List Actor) : Nat → FightState → Roll (Option FightState)
  | fuel, state => do
    if state.over then return some state
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      let living := (state.foes.zipIdx.filter fun (f, _) => f.alive).map Prod.snd
      let target := living.getD (← choose living.length) 0
      let (next, _) ← fightRound rules order state target
      fight rules order fuel next

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
        let level := (a.hero.rollLevel a.rules target).map (· + modifier)
        let (result, _) ← makeRoll a.rules "audit" level
        trajectory a roundLimit fuel (if result.succeeded then yes else no) hp (turns + 1)
      | .fight foes next =>
        let state : FightState := ⟨⟨a.hero, hp⟩, foes.map fun foe => ⟨foe, a.rules.maxHP foe⟩⟩
        let result ← fight a.rules (turnOrder a.rules a.hero foes) roundLimit state
        match result with
        | none => return ⟨.censored, turns + 1⟩
        | some state =>
          if !state.hero.alive then return ⟨.dead, turns + 1⟩
          trajectory a roundLimit fuel next state.hero.hp (turns + 1)

end Rpg.Probability.Simulation
