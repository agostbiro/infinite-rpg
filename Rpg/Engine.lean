import Rpg.Adventure

/-!
# Engine

The Engine rolls all dice and works out every result.
It is pure code: dice come from a seeded random number generator (`Rng`),
so the same seed always gives the same game.

A Fight runs in rounds. In each round, every living being acts once,
in order of Basic Speed, then DX. The Character wins any tie that is left.
On its turn, a being attacks. The defender may Dodge.
-/

namespace Rpg

/-- A seeded random number generator (SplitMix64). -/
structure Rng where
  state : UInt64

/-- The next random 64-bit number. -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Engine steps that use dice. -/
abbrev Roll := StateM Rng

/-- Roll one six-sided die. -/
def d6 : Roll Nat := do
  let (x, g) := (← get).next
  set g
  return x.toNat % 6 + 1

/-- Roll `n` six-sided dice and add them. -/
def rollDice : Nat → Roll Nat
  | 0 => return 0
  | n + 1 => do
    let a ← d6
    let b ← rollDice n
    return a + b

/-- Roll 3d6. -/
def roll3d6 : Roll Nat := rollDice 3

/-- The display name of a roll result. -/
def RollResult.name : RollResult → String
  | .criticalSuccess => "critical success"
  | .success => "success"
  | .failure => "failure"
  | .criticalFailure => "critical failure"

/-- Make a Success Roll at an effective skill. Returns the result and a line of text.
`none` means the being cannot use the skill at all. Then, and also when the effective skill
is below 3, there is no roll and the result is a failure (p. 2, and deviation 7).
A Legal Adventure never asks for such a roll (see `CanTryRoll` in the spec). -/
def makeRoll (label : String) (skill? : Option Int) : Roll (RollResult × String) := do
  let some skill := skill?
    | return (.failure, s!"{label}: you cannot use this skill untrained. Failure.")
  if skill < 3 then
    return (.failure, s!"{label}: effective skill {skill} is too low to try. Failure.")
  let r ← roll3d6
  let res := successRoll skill r
  return (res, s!"{label} (needs {skill} or less): rolled {r}, {res.name}.")

/-- A being in a Fight, with its current HP. -/
structure Fighter where
  being : Being
  hp : Int

/-- A Fighter is alive while it has more than 0 HP (see deviation 1). -/
def Fighter.alive (f : Fighter) : Bool := f.hp > 0

/-- Dodge, halved (rounded up) when the being has less than 1/3 of its HP left (p. 29). -/
def Fighter.dodge (f : Fighter) : Nat :=
  let d := f.being.dodge
  if 3 * f.hp < f.being.maxHP then (d + 1) / 2 else d

/-- One attack by `att` on `def`. Returns the injury done and lines of text. -/
def attack (att : Fighter) (dfn : Fighter) : Roll (Nat × List String) := do
  let level := att.being.attackLevel
  if level < 3 then
    return (0, [s!"{att.being.name} cannot attack: effective skill {level} is too low to try."])
  let r ← roll3d6
  let res := successRoll level r
  let line := s!"{att.being.name} attacks {dfn.being.name} with {att.being.weapon.name} (needs {level} or less): rolled {r}, {res.name}."
  if !res.succeeded then
    return (0, [line])
  let mut lines := [line]
  if res != .criticalSuccess then
    let dr ← roll3d6
    -- A defense roll has no critical results: it just succeeds or fails (p. 28).
    let dodged := (successRoll dfn.dodge dr).succeeded
    lines := lines ++ [s!"  {dfn.being.name} dodges (needs {dfn.dodge} or less): rolled {dr}, {if dodged then "success" else "failure"}."]
    if dodged then
      return (0, lines)
  let dice := att.being.weapon.damage att.being.st
  let sum ← if r = 3 then pure (6 * dice.count) else rollDice dice.count
  let basic := basicDamage dice att.being.weapon.damageType sum
  let inj := injury att.being.weapon.damageType dfn.being.dr basic
  lines := lines ++ [s!"  Hit! {basic} damage, DR {dfn.being.dr}, {inj} injury."]
  return (inj, lines)

/-- The state of a Fight: the Character and the Creatures. -/
structure FightState where
  hero : Fighter
  foes : List Fighter

/-- The Fight is over when the Character is dead or every Creature is dead. -/
def FightState.over (s : FightState) : Bool :=
  !s.hero.alive || s.foes.all (!·.alive)

/-- Who acts in a round: `none` is the Character, `some i` is Creature number `i`. -/
abbrev Actor := Option Nat

/-- `true` if `a` acts before `b`: higher Basic Speed first, then higher DX. -/
def actsBefore (a b : Being × Bool) : Bool :=
  if a.1.speedX4 != b.1.speedX4 then a.1.speedX4 > b.1.speedX4
  else if a.1.dx != b.1.dx then a.1.dx > b.1.dx
  else a.2

/-- The turn order for a Fight. It is set at the start and does not change (p. 24). -/
def turnOrder (hero : Being) (foes : List Being) : List Actor :=
  let all : List (Actor × Being × Bool) :=
    (none, hero, true) :: (foes.zipIdx.map fun (b, i) => (some i, b, false))
  (all.mergeSort fun x y => actsBefore x.2 y.2).map (·.1)

/-- Change the HP of Creature number `i`. -/
def hurtFoe (foes : List Fighter) (i : Nat) (inj : Nat) : List Fighter :=
  foes.modify i fun f => { f with hp := f.hp - inj }

/-- One turn of one actor. The Character attacks Creature number `target`. Each Creature attacks the Character. -/
def takeTurn (s : FightState) (target : Nat) (who : Actor) : Roll (FightState × List String) := do
  if s.over then return (s, [])
  match who with
  | none =>
    match s.foes[target]? with
    | some foe =>
      if !foe.alive then return (s, [])
      let (inj, lines) ← attack s.hero foe
      return ({ s with foes := hurtFoe s.foes target inj }, lines)
    | none => return (s, [])
  | some i =>
    match s.foes[i]? with
    | some foe =>
      if !foe.alive then return (s, [])
      let (inj, lines) ← attack foe s.hero
      return ({ s with hero := { s.hero with hp := s.hero.hp - inj } }, lines)
    | none => return (s, [])

/-- One round of a Fight: every actor takes a turn in turn order. -/
def fightRound (order : List Actor) (s : FightState) (target : Nat) : Roll (FightState × List String) := do
  let mut st := s
  let mut log : List String := []
  for who in order do
    let (st', lines) ← takeTurn st target who
    st := st'
    log := log ++ lines
  return (st, log)

end Rpg
