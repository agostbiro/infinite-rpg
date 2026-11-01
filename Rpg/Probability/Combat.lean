import Rpg.Engine
import Rpg.Probability.Distribution

/-!
Combat probabilities use the same attack and actor-turn functions as play.
Every living target is chosen uniformly. Self-loops (rounds with no HP change)
are eliminated geometrically, rather than imposing a round limit.
-/
namespace Rpg.Probability

/-- The result of a fight, including surviving HP or a fight that never finishes. -/
inductive CombatResult where
  | won (hp : Int)
  | died
  | stalled
  deriving DecidableEq, Repr

/-- One attack under the adventure rules, merging equal injuries and discarding display logs. -/
def attackDistribution (rules : RuleSet) (att dfn : Fighter) : Distribution (Nat × List String) :=
  ((fun result => (result.1, ([] : List String))) <$> attackWith rules dice att dfn).collect

/-- One actor's turn, with equal resulting combat states merged. -/
def actorDistribution (rules : RuleSet) (s : FightState) (target : Nat) (who : Actor) : Distribution FightState :=
  (Prod.fst <$> takeTurnWith (attackDistribution rules) s target who).collect

/-- Interpret a full round in the engine's turn order. -/
def roundActors (rules : RuleSet) (target : Nat) : List Actor → FightState → Distribution FightState
  | [], s => pure s
  | who :: rest, s =>
    ((actorDistribution rules s target who).bind (roundActors rules target rest)).collect

/-- A round chooses uniformly among living enemies, then runs every actor. -/
def roundDistribution (rules : RuleSet) (s : FightState) : Distribution FightState :=
  let targets := (s.foes.zipIdx.filter fun (f, _) => f.alive).map Prod.snd
  let order := turnOrder rules s.hero.being (s.foes.map Fighter.being)
  ((uniform targets).bind fun target => roundActors rules target order s).collect

/-- Total living HP; every non-self transition in a valid fight decreases it. -/
def livingHP (s : FightState) : Nat :=
  s.hero.hp.toNat + (s.foes.map fun f => f.hp.toNat).sum

/-- A memo table avoids solving the same injured combat state repeatedly. -/
abbrev CombatCache := List (FightState × Distribution CombatResult)

/-- Solve a fight by eliminating unchanged rounds and recurring on lower HP.
A nondecreasing, non-self transition is reported as stalled, never as a win.
The shared engine only removes HP, so that defensive branch is not used in play. -/
def solveCombat (rules : RuleSet) (s : FightState) : StateM CombatCache (Distribution CombatResult) := do
  if !s.hero.alive then return pure .died
  if s.foes.all (!·.alive) then return pure (.won s.hero.hp)
  if let some entry := (← get).find? (fun e => decide (e.1 = s)) then
    return entry.2
  let edges := roundDistribution rules s
  let stay := edges.mass (fun next => decide (next = s))
  if stay = 1 then return pure .stalled
  let mut result : List (CombatResult × Rat) := []
  for (next, weight) in edges.entries do
    if next ≠ s ∧ weight ≠ 0 then
      let continuation ← if _h : livingHP next < livingHP s then
          solveCombat rules next
        else pure (pure .stalled)
      result := result ++ continuation.entries.map fun (outcome, p) =>
        (outcome, weight * p / (1 - stay))
  let answer := (Distribution.mk result).collect
  modify ((s, answer) :: ·)
  return answer
termination_by livingHP s

/-- Exact fight outcome distribution for a hero arriving with the given HP. -/
def combatDistribution (rules : RuleSet) (hero : Being) (hp : Int) (foes : List Being) : Distribution CombatResult :=
  (solveCombat rules ⟨⟨hero, hp⟩, foes.map fun foe => ⟨foe, rules.maxHP foe⟩⟩).run' []

end Rpg.Probability
