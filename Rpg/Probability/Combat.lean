import Rpg.Engine
import Rpg.Probability.Distribution
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Rpg.Probability.Parallel

/-!
# Exact Fight odds

This producer proposes rational Fight result probabilities. `CombatCertificate.lean`
independently verifies them before the graph or admission trusts them. It uses the same Engine
functions as play (`attackWith`, `heroTurnWith`, `foeTurnsWith`), in the same turn order
(`beforeCharacter`, then the Character, then `afterCharacter`), with exact dice odds.

The model's Player is `heroPolicy`: on each turn it picks Attack, All-Out Attack, or
All-Out Defense, each with chance 1/3. If the maneuver attacks, it picks a living Creature,
each with the same chance. Creatures always Attack.

A round can take HP, or it can leave all HP the same. The Engine never adds HP. So the solver
works on a **group**: every state that rounds can reach from a state without any HP loss.
States in a group differ only in the Character's last maneuver, so a group has at most 3 states.
The solver writes one linear equation for each state in the group, and solves them exactly.
Every way out of the group loses HP, so a group needs only the answers of states with less
total HP. `solveCombatAnswer` calls itself on those states. `solveFight` solves all groups of
one total HP at the same time, from low HP to high. A group that never loses HP is a Fight that
never ends (`stalled`).
-/
namespace Rpg.Probability

/-- The result of a Fight: the Character wins with this much HP, dies, or the Fight never ends. -/
inductive CombatResult where
  | won (hp : Int)
  | died
  | stalled
  deriving DecidableEq, Repr

/-- `n` dice, as a one-item list that holds only their sum. The Engine uses only the sum of the
faces to decide a result, so this gives the same results as rolling each die, with fewer cases. -/
def sumAsFaces (n : Nat) : Distribution (List Nat) :=
  (fun total => [total]) <$> dice n

/-- One attack under `rules`, with exact dice odds. Equal injuries are merged, and the Reports are
dropped, because the model needs only the injury. -/
def attackDistribution (rules : RuleSet) : AttackFn Distribution :=
  fun attId att dfnId dfn =>
    (fun inj => (inj, ([] : List Report))) <$>
      ((Prod.fst <$> attackWith rules sumAsFaces attId att dfnId dfn).collect)

/-- The numbers of the Creatures that are alive. -/
def livingTargets (s : FightState) : List Nat :=
  s.livingFoes

/-- The model's Player: each maneuver with chance 1/3, then a living target with equal chances
if the maneuver attacks. A maneuver with no attack has no target, so it uses 0. -/
def heroPolicy (s : FightState) : Distribution (Maneuver × Nat) :=
  (uniform maneuverMenu).bind fun m =>
    if m.attacks then (uniform (livingTargets s)).bind fun t => pure (m, t)
    else pure (m, 0)

/-- A Player that always Attacks a living target, with equal chances. The old model (before
maneuvers) used this Player. With it, the new solver gave exactly the old solver's odds on the
Lighthouse Fights. That was a one-off check in the merge (ADR 0004), not a build test, because
those Fights take minutes to solve. -/
def attackOnlyPolicy (s : FightState) : Distribution (Maneuver × Nat) :=
  (uniform (livingTargets s)).bind fun t => pure (.attack, t)

/-- The Creature turns in `actors`, one at a time, with equal states merged after each turn. -/
def foesDistribution (rules : RuleSet) : FightState → List Actor → Distribution FightState
  | s, [] => pure s
  | s, a :: rest =>
    (((Prod.fst <$> foeTurnsWith (attackDistribution rules) s [a]).collect).bind
      fun s => foesDistribution rules s rest).collect

/-- One round in turn order `order`, with exact odds. This is `roundWith` with equal states
merged after each turn, so that the number of cases stays small. -/
def roundDistribution (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) : Distribution FightState :=
  let before := foesDistribution rules s (beforeCharacter order)
  let mine := (before.bind fun s =>
    if s.over then pure s
    else (policy s).bind fun (m, t) => Prod.fst <$> heroTurnWith (attackDistribution rules) s m t).collect
  (mine.bind fun s => foesDistribution rules s (afterCharacter order)).collect

/-- The HP of every being that is alive, added up. Every round either takes HP or leaves it the same. -/
def livingHP (s : FightState) : Nat :=
  s.hero.hp.toNat + (s.foes.map fun f => f.hp.toNat).sum

/-- The only three states possible without HP loss. Keep the queried state first.
No search fuel is needed; the certificate checker verifies closure of the full result. -/
def maneuverStates (s : FightState) : List FightState :=
  s :: ((maneuverMenu.filter (· != s.hero.maneuver)).map fun m =>
    {s with hero := {s.hero with maneuver := m}})

/-- Results with weights. The weights need not add up to 1. -/
abbrev Weighted := List (CombatResult × Rat)

/-- Multiply every weight by `c`. -/
def Weighted.scale (c : Rat) (w : Weighted) : Weighted :=
  w.map fun (x, p) => (x, c * p)

/-- Add `c` times the weights of `v` to `w`, and merge equal results. A Fight has few results,
so the lists stay short. -/
def Weighted.addScaled (w : Weighted) (c : Rat) (v : Weighted) : Weighted :=
  v.foldl (fun acc (x, p) => addWeight x (c * p) acc) w

/-- Solve the linear system `m · x = b` by Gauss-Jordan elimination. Each `x` and `b` is a list of
weighted results. `m` must have an inverse. Rows with no pivot keep their `b`. -/
def solveLinear (m : Array (Array Rat)) (b : Array Weighted) : Array Weighted := Id.run do
  let n := m.size
  let mut m := m
  let mut b := b
  for k in [:n] do
    let some p := (List.range n).find? (fun r => k ≤ r && m[r]![k]! != 0) | continue
    -- Swap rows `k` and `p`.
    let (rk, rp, bk, bp) := (m[k]!, m[p]!, b[k]!, b[p]!)
    m := (m.set! k rp).set! p rk
    b := (b.set! k bp).set! p bk
    -- Divide row `k` by its pivot.
    let piv := m[k]![k]!
    m := m.set! k (m[k]!.map (· / piv))
    b := b.set! k (b[k]!.scale (1 / piv))
    -- Take row `k` away from every other row, so that column `k` is zero there.
    for r in [:n] do
      let f := m[r]![k]!
      if r != k && f != 0 then
        let row := m[k]!
        m := m.set! r ((Array.range n).map fun j => m[r]![j]! - f * row[j]!)
        b := b.set! r (b[r]!.addScaled (-f) b[k]!)
  return b

/-- The results of each state in a group.
`stay i j` is the chance that one round goes from state `i` to state `j` of the group.
`leave i` is the chance that one round goes from state `i` to a state outside the group,
and `exits i` are the results of those rounds, already weighted by their chances.
A state that can never leave the group is a Fight that never ends. -/
def solveGroup (n : Nat) (stay : Nat → Nat → Rat) (leave : Nat → Rat) (exits : Nat → Weighted) :
    List (Distribution CombatResult) := Id.run do
  -- Find the states that can leave the group, in one round or more.
  let mut canLeave : Array Bool := (Array.range n).map fun i => leave i != 0
  for _ in [:n] do
    canLeave := (Array.range n).map fun i =>
      canLeave[i]! || (List.range n).any fun j => stay i j != 0 && canLeave[j]!
  let live := (List.range n).filter (canLeave[·]!)
  -- For each state that can leave: x i = Σ stay i j · x j + exits i. A state that cannot
  -- leave has the result `stalled`.
  let m : Array (Array Rat) := live.toArray.map fun i =>
    live.toArray.map fun j => (if i = j then 1 else 0) - stay i j
  let b : Array Weighted := live.toArray.map fun i =>
    exits i ++ (List.range n).filterMap fun j =>
      if canLeave[j]! then none else some (.stalled, stay i j)
  let x := solveLinear m b
  return (List.range n).map fun i =>
    match live.idxOf? i with
    | some k => (Distribution.mk (x[k]!)).collect
    | none => pure .stalled

/-- Candidate results and a candidate bound on expected remaining rounds.
These are solver output; `CombatCertificate` independently checks their equations. -/
structure CombatAnswer where
  outcomes : Distribution CombatResult
  rounds : Rat

/-- A small number for a maneuver. -/
def _root_.Rpg.Maneuver.index : Maneuver → Nat
  | .attack => 0
  | .allOutAttack => 1
  | .allOutDefense => 2

/-- A number made from the HP and the last maneuver of a Fighter. -/
def fighterCode (f : Fighter) : Nat :=
  ((f.hp + 512).toNat % 1024) * 4 + f.maneuver.index

/-- A number made from the HP and the last maneuver of each Fighter, used to sort states.
Equal states get equal numbers. Different states can get the same number. -/
def stateKey (s : FightState) : Nat :=
  s.foes.foldl (fun acc f => acc * 4096 + fighterCode f) (fighterCode s.hero)

/-- The hash of a state mixes the code of each Fighter, so that no Fighter is lost when a Fight
has many Creatures. -/
instance : Hashable FightState :=
  ⟨fun s => s.foes.foldl (fun h f => mixHash h (hash (fighterCode f))) (hash (fighterCode s.hero))⟩

/-- The solved states, with their answers. -/
abbrev CombatCache := Std.HashMap FightState CombatAnswer

/-- Reuse the elimination algorithm for a single scalar coordinate. The marker is
only a coordinate label; these weights are not a probability distribution. -/
def solveScalar (m : Array (Array Rat)) (b : Array Rat) : Array Rat :=
  (solveLinear m (b.map fun x => [(CombatResult.died, x)])).map fun row => (row.map Prod.snd).sum

/-- The answer that the solver knows for `w`: an ended Fight has its result, and a state with
no answer in `cache` gets `stalled`. -/
def knownAnswer (cache : CombatCache) (w : FightState) : CombatAnswer :=
  if !w.hero.alive then ⟨pure .died, 0⟩
  else if w.foes.all (!·.alive) then ⟨pure (.won w.hero.hp), 0⟩
  else cache.getD w ⟨pure .stalled, 0⟩

/-- Solve one group. `rounds` are the rounds of the states of `group`, in the same order.
`exitAnswer` gives the answer of each state outside the group that a round can reach. -/
def groupAnswers (group : List FightState) (rounds : List (Distribution FightState))
    (exitAnswer : FightState → CombatAnswer) : List CombatAnswer := Id.run do
  let mut exits : Array Weighted := #[]
  let mut costs : Array Rat := #[]
  for d in rounds do
    let mut acc : Weighted := []
    let mut cost : Rat := 1
    for (w, p) in d.entries do
      if p ≠ 0 ∧ w ∉ group then
        let r := exitAnswer w
        acc := acc.addScaled p r.outcomes.entries
        cost := cost + p * r.rounds
    exits := exits.push acc
    costs := costs.push cost
  let n := group.length
  let stay (i j : Nat) : Rat :=
    match rounds[i]?, group[j]? with
    | some d, some v => d.mass fun u => decide (u = v)
    | _, _ => 0
  let leave (i : Nat) : Rat :=
    match rounds[i]? with
    | some d => d.mass fun u => decide (u ∉ group)
    | none => 0
  let answers := solveGroup n stay leave (exits[·]!)
  let matrix := (Array.range n).map fun i => (Array.range n).map fun j =>
    (if i = j then 1 else 0) - stay i j
  let budgets := solveScalar matrix costs
  return answers.zip budgets.toList |>.map fun (outcomes, rounds) => ({outcomes, rounds} : CombatAnswer)

/-- Generate candidate answers by HP recursion and three-state elimination. `round` gives the
odds of one round. Correctness of this producer is not trusted by the certificate checker. -/
def solveCombatAnswer (round : FightState → Distribution FightState) (s : FightState) :
    StateM CombatCache CombatAnswer := do
  if !s.hero.alive then return ⟨pure .died, 0⟩
  if s.foes.all (!·.alive) then return ⟨pure (.won s.hero.hp), 0⟩
  if let some answer := (← get)[s]? then
    return answer
  let group := maneuverStates s
  let rounds := group.map round
  for d in rounds do
    for (w, p) in d.entries do
      if p ≠ 0 ∧ w ∉ group then
        -- A malformed transition can produce a candidate, but cannot pass the
        -- independently checked closure and expected-duration inequalities.
        if _h : livingHP w < livingHP s then
          discard <| solveCombatAnswer round w
  let cache ← get
  let solutions := groupAnswers group rounds fun w =>
    if livingHP w < livingHP s then knownAnswer cache w else ⟨pure .stalled, 0⟩
  for (u, a) in group.zip solutions do
    modify (·.insert u a)
  return solutions.headD ⟨pure .stalled, 0⟩
termination_by livingHP s

/-- The state that names the group of `s`: the same state, with the Character's last maneuver
set to Attack. -/
def groupName (s : FightState) : FightState :=
  {s with hero := {s.hero with maneuver := .attack}}

/-- Limits on the work of `solveFight`. Above a limit, it gives up and returns no answers, so the
check fails and the Fight is rejected. Only `entries` is tested after the fact, so one batch, at
most `batchEntries` results, can go above it. -/
structure SolveBudget where
  /-- The most states that the solver solves. -/
  states : Nat := 60000
  /-- The most round results that the solver keeps in memory at one time. -/
  entries : Nat := 1500000
  /-- The most results that one round may make before they are merged, by the bound that the
  solver gets. A larger round is not computed. A Fight with such rounds could do at most 50 of
  them within `work`, too few to finish. -/
  roundEntries : Nat := 200000
  /-- The most results, by the bound, of the rounds that the solver computes at the same time. -/
  batchEntries : Nat := 1000000
  /-- The most results, by the bound, of all the rounds that the solver computes. It stops a
  large Fight after a small part of its work. -/
  work : Nat := 10000000

/-- Split `xs` into batches, in order. A batch has at most `count` items, and the sum of `cost`
over a batch is at most `limit`, unless the batch has only one item. -/
def batchesBy (cost : α → Nat) (limit count : Nat) (xs : List α) : List (List α) :=
  let (done, current, _) := xs.foldl (fun (done, current, total) x =>
    let c := cost x
    if !current.isEmpty && (total + c > limit || current.length ≥ count) then
      (current.reverse :: done, [x], c)
    else (done, x :: current, total + c)) ([], [], 0)
  (if current.isEmpty then done else current.reverse :: done).reverse

/-- The batches in which `solveFight` computes the rounds of the groups in `frontier`, each
state with its bound by `size`. It is `none` if one bound is above `budget.roundEntries` or
`budget.batchEntries`. Each item is one state, not one group, so the bounds in a batch add up to
at most `budget.batchEntries`. -/
def planRounds (size : FightState → Nat) (budget : SolveBudget) (frontier : List FightState) :
    Option (List (List (FightState × Nat))) :=
  let states := frontier.flatMap maneuverStates
  let sized := states.zip (parallelMap size states)
  if sized.any (·.2 > min budget.roundEntries budget.batchEntries) then none
  else some (batchesBy Prod.snd budget.batchEntries 144 sized)

/-- Find candidate answers for every state that the Fight can reach from `starts`, on many cores.
`size` bounds the results of a round before it is computed, so a Fight over `budget` stops early.
The certificate checker does not trust these answers. -/
def solveFight (round : FightState → Distribution FightState) (starts : List FightState)
    (size : FightState → Nat) (budget : SolveBudget := {}) : CombatCache := Id.run do
  let mut seen : Std.HashSet FightState := {}
  let mut frontier : List FightState := []
  for s in starts do
    let g := groupName s
    if !s.over && !seen.contains g then
      seen := seen.insert g
      frontier := g :: frontier
  -- Find the groups that the Fight can reach, and the round of each of their states.
  -- A round that leaves a group takes HP, so a shortest path to a group has at most as many
  -- steps as the total HP. That bounds the number of passes.
  let passes := (starts.map livingHP).foldl max 0 + 2
  let mut rounds : Std.HashMap FightState (Distribution FightState) := {}
  let mut levels : Std.HashMap Nat (List FightState) := {}
  let mut kept := 0
  let mut work := 0
  for _ in [:passes] do
    if frontier.isEmpty then break
    -- Give up before any work on the frontier if it has too many states. Each group has 3.
    if 3 * seen.size > budget.states then return {}
    let mut next : List FightState := []
    for g in frontier do
      levels := levels.alter (livingHP g) fun l => some (g :: l.getD [])
    -- Work in batches, so that a Fight that is too large stops before it uses much memory.
    -- Bound the round of each state before any of them is computed.
    let some batches := planRounds size budget frontier | return {}
    for batch in batches do
      -- Give up when the Fight is too large. Each group has 3 states.
      work := work + (batch.map Prod.snd).sum
      if 3 * seen.size > budget.states || kept > budget.entries || work > budget.work then
        return {}
      let found := parallelMap (fun u => (u, round u)) (batch.map Prod.fst)
      for (u, d) in found do
        rounds := rounds.insert u d
        kept := kept + d.entries.length
        for (w, _) in d.entries do
          let r := groupName w
          if !w.over && !seen.contains r then
            seen := seen.insert r
            next := r :: next
            if 3 * seen.size > budget.states then return {}
    frontier := next
  if 3 * seen.size > budget.states || kept > budget.entries || !frontier.isEmpty then return {}
  -- Solve the groups, from the lowest total HP up.
  let mut cache : CombatCache := {}
  for (_, groups) in levels.toList.mergeSort (fun a b => a.1 ≤ b.1) do
    let known := cache
    let solved := parallelMap (fun g =>
      let group := maneuverStates g
      group.zip (groupAnswers group (group.map fun u => rounds.getD u (pure u)) (knownAnswer known)))
      groups
    for members in solved do
      for (u, a) in members do
        cache := cache.insert u a
  return cache

/-- Compatibility entry point for the candidate solver. Use certification when a
probabilistic guarantee is required. -/
def solveCombat (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (order : List Actor) (s : FightState) : StateM CombatCache (Distribution CombatResult) := do
  return (← solveCombatAnswer (roundDistribution rules policy order) s).outcomes

/-- Unverified candidate odds for a Character at `hp` against `foes`.
Use `checkedCombat` or a `CertifiedFight` for probability guarantees. -/
def combatDistributionWith (rules : RuleSet) (policy : FightState → Distribution (Maneuver × Nat))
    (hero : Being) (hp : Int) (foes : List Being) : Distribution CombatResult :=
  let start : FightState :=
    { hero := { being := hero, hp }, foes := foes.map fun f => { being := f, hp := rules.maxHP f } }
  (solveCombat rules policy (turnOrder rules hero foes) start).run' {}

/-- Unverified candidate odds for `heroPolicy`; kept for producer diagnostics. -/
def combatDistribution (rules : RuleSet) (hero : Being) (hp : Int) (foes : List Being) :
    Distribution CombatResult :=
  combatDistributionWith rules heroPolicy hero hp foes

/-! ## Tests -/

-- A 2-state group: state 0 stays with 1/2, goes to state 1 with 1/4, and leaves with 1/4 to a win.
-- State 1 goes to state 0 with 1/2, and leaves with 1/2 to a death. The exact answers are
-- x0 = 2/3 win, 1/3 death and x1 = 1/3 win, 2/3 death.
#guard
  let stay (i j : Nat) : Rat := match i, j with
    | 0, 0 => 1/2 | 0, 1 => 1/4 | 1, 0 => 1/2 | _, _ => 0
  let leave (i : Nat) : Rat := if i = 0 then 1/4 else 1/2
  let exits (i : Nat) : Weighted := if i = 0 then [(.won 1, 1/4)] else [(.died, 1/2)]
  let xs := solveGroup 2 stay leave exits
  xs.map (fun x => (x.mass (· == .won 1), x.mass (· == .died))) == [(2/3, 1/3), (1/3, 2/3)]

-- A group that never leaves is a Fight that never ends.
#guard
  let xs := solveGroup 2 (fun i j => if i ≠ j then 1 else 0) (fun _ => 0) (fun _ => [])
  xs.map (·.mass (· == .stalled)) == [1, 1]

/-- A test being with 1 HP and a broadsword at skill 12. -/
private def frail (name : String) : Being :=
  { name, st := 1, dx := 10, iq := 10, ht := 10, skills := [(.broadsword, 12)],
    weapon := .broadsword, armor := .none }

-- In a Fight between two 1-HP beings, the odds add up to 1, and both results can happen.
#guard
  let d := combatDistribution {} (frail "Hero") 1 [frail "Foe"]
  d.mass (fun _ => true) == 1 && 0 < d.mass (· == .died) && 0 < d.mass (· == .won 1)

end Rpg.Probability
