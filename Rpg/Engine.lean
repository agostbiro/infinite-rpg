import Rpg.Adventure

/-!
# Engine

The Engine rolls all dice and works out every result.
It is pure code: dice come from a seeded random number generator (`Rng`),
so the same seed always gives the same game.

A Fight runs in rounds. In each round, every living being acts once,
in order of Basic Speed, then DX. The Character wins any tie that is left.
On its turn, a being chooses a maneuver: Attack, All-Out Attack, or All-Out Defense.
Each Creature always chooses Attack. A maneuver includes at most one attack.
The defender may Dodge, unless its own last maneuver was an All-Out Attack.
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

/-- A being in a Fight, with its current HP and its last maneuver. -/
structure Fighter where
  being : Being
  hp : Int
  /-- The maneuver from the being's last turn. It sets the being's defense (p. 25).
  Before its first turn, a being counts as doing nothing, which defends like Attack. -/
  maneuver : Maneuver := .attack

/-- A Fighter is alive while it has more than 0 HP (see deviation 1). -/
def Fighter.alive (f : Fighter) : Bool := f.hp > 0

/-- The Dodge score of a Fighter now, or `none` if it cannot defend.
Dodge is halved (rounded up) when the being has less than 1/3 of its HP left (p. 29).
Then the bonus from the last maneuver is added. -/
def Fighter.dodge (f : Fighter) : Option Nat :=
  let d := f.being.dodge
  let base := if 3 * f.hp < f.being.maxHP then (d + 1) / 2 else d
  f.maneuver.dodgeBonus.map (base + ·)

/-- One attack by `att` on `dfn`. The last maneuver of `att` gives the bonus to hit.
Returns the injury done and lines of text. -/
def attack (att : Fighter) (dfn : Fighter) : Roll (Nat × List String) := do
  let level := att.being.attackLevel + att.maneuver.hitBonus
  if level < 3 then
    return (0, [s!"{att.being.name} cannot attack: effective skill {level} is too low to try."])
  let r ← roll3d6
  let res := successRoll level r
  let line := s!"{att.being.name} attacks {dfn.being.name} with {att.being.weapon.name} (needs {level} or less): rolled {r}, {res.name}."
  if !res.succeeded then
    return (0, [line])
  let mut lines := [line]
  if res != .criticalSuccess then
    match dfn.dodge with
    | none =>
      lines := lines ++ [s!"  {dfn.being.name} cannot defend after an All-Out Attack."]
    | some dodge =>
      let dr ← roll3d6
      -- A defense roll has no critical results: it just succeeds or fails (p. 28).
      let dodged := (successRoll dodge dr).succeeded
      lines := lines ++ [s!"  {dfn.being.name} dodges (needs {dodge} or less): rolled {dr}, {if dodged then "success" else "failure"}."]
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

/-- A line of text that says which maneuver a being chose. Attack needs no line. -/
def announce (name : String) (m : Maneuver) : List String :=
  if m = .attack then [] else [s!"{name} chooses {m.describe}."]

/-- The Character's turn. The Character uses maneuver `choice`. If the maneuver includes
an attack, the Character attacks Creature number `target`. A dead or missing target makes
the turn do nothing. -/
def heroTurn (s : FightState) (choice : Maneuver) (target : Nat) :
    Roll (FightState × List String) := do
  if s.over then return (s, [])
  let hero := { s.hero with maneuver := choice }
  let intro := announce hero.being.name choice
  if !choice.attacks then return ({ s with hero := hero }, intro)
  let some foe := s.foes[target]? | return (s, [])
  if !foe.alive then return (s, [])
  let (inj, lines) ← attack hero foe
  return ({ s with hero := hero, foes := hurtFoe s.foes target inj }, intro ++ lines)

/-- The turn of Creature number `i`. A Creature always chooses Attack and attacks the Character. -/
def foeTurn (s : FightState) (i : Nat) : Roll (FightState × List String) := do
  if s.over then return (s, [])
  let some foe := s.foes[i]? | return (s, [])
  if !foe.alive then return (s, [])
  let (inj, lines) ← attack foe s.hero
  return ({ s with hero := { s.hero with hp := s.hero.hp - inj } }, lines)

/-! ## Tests -/

/-- A test being with Dodge 9, 12 HP, and no armor. -/
private def testBeing : Being :=
  { name := "Test", st := 12, dx := 12, iq := 10, ht := 12,
    skills := [(.broadsword, 12)], weapon := .broadsword, armor := .none }

-- Dodge with each maneuver, at full HP and below 1/3 HP.
#guard ({ being := testBeing, hp := 12 } : Fighter).dodge == some 9
#guard ({ being := testBeing, hp := 12, maneuver := .allOutDefense } : Fighter).dodge == some 11
#guard ({ being := testBeing, hp := 3, maneuver := .allOutDefense } : Fighter).dodge == some 7
#guard ({ being := testBeing, hp := 12, maneuver := .allOutAttack } : Fighter).dodge == none

/-- A Fight between two test beings, with the Character's last maneuver set to `m`. -/
private def testFight (m : Maneuver) : FightState :=
  ⟨{ being := testBeing, hp := 12, maneuver := m }, [{ being := testBeing, hp := 12 }]⟩

-- Halved Dodge with no maneuver bonus: 9 halves to 5.
#guard ({ being := testBeing, hp := 3 } : Fighter).dodge == some 5

-- All-Out Defense: the Character does not attack, and the maneuver is stored.
#guard
  let (s, lines) := (heroTurn (testFight .attack) .allOutDefense 0).run' ⟨7⟩
  s.foes.map (·.hp) == [12] && s.hero.maneuver == .allOutDefense &&
    lines == ["Test chooses All-Out Defense: no attack, but +2 to Dodge until the next turn."]

-- After an All-Out Attack, the Character never dodges, and for some seeds it is hit with no defense.
#guard
  let logs := (List.range 50).map fun seed =>
    ((foeTurn (testFight .allOutAttack) 0).run' ⟨seed.toUInt64⟩).2
  logs.all (·.all (!·.startsWith "  Test dodges")) &&
    logs.any (·.contains "  Test cannot defend after an All-Out Attack.")

/-- The Character makes an All-Out Attack, then an Attack, then the Creature attacks. Returns the Creature's lines. -/
private def attackAfterAllOut : Roll (List String) := do
  let (s, _) ← heroTurn (testFight .attack) .allOutAttack 0
  let (s, _) ← foeTurn s 0
  let (s, _) ← heroTurn s .attack 0
  let (_, lines) ← foeTurn s 0
  return lines

-- An Attack after an All-Out Attack gives the defense back: for some seeds the Character dodges.
#guard (List.range 50).any fun seed =>
  (attackAfterAllOut.run' ⟨seed.toUInt64⟩).any (·.startsWith "  Test dodges")

-- All-Out Attack adds 4 to the attack roll: Broadsword-12 needs 16 or less.
#guard
  let (_, lines) := (heroTurn (testFight .attack) .allOutAttack 0).run' ⟨1⟩
  lines.any (·.startsWith "Test attacks Test with broadsword (needs 16 or less)")

end Rpg
