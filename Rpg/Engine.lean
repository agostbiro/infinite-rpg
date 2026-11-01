import Rpg.Report

/-!
# Engine

The Engine rolls all dice and works out every result.
It is pure code: dice come from a seeded random number generator (`Rng`),
so the same seed always gives the same game.
Each step returns Reports (see `Rpg/Report.lean`) that say what happened, with every die face.

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

/-- Roll `n` six-sided dice. Returns each face. The total is the sum of the faces. -/
def rollDice : Nat → Roll (List Nat)
  | 0 => return []
  | n + 1 => do
    let a ← d6
    let rest ← rollDice n
    return a :: rest

/-- Roll 3d6. Returns the three faces. -/
def roll3d6 : Roll (List Nat) := rollDice 3

/-- Roll 3d6 against a target number, with the dice from `roll`.
`roll n` rolls `n` six-sided dice and gives the faces. The Engine uses only the sum of the faces
to decide a result, so the fairness model can pass one-item lists that hold only the sum. -/
def rollAgainstWith [Monad m] (rules : RuleSet) (roll : Nat → m (List Nat)) (target : Int) :
    m DiceRoll := do
  let faces ← roll 3
  return ⟨faces, faces.sum, target, rules.successRoll target faces.sum⟩

/-- Roll 3d6 against a target number, with the seeded dice. -/
def rollAgainst (rules : RuleSet) (target : Int) : Roll DiceRoll :=
  rollAgainstWith rules rollDice target

/-- Make a Success Roll for `who` against `target` at `modifier`, at an effective skill.
Returns the result and a Report.
`none` means the being cannot use the skill at all. Then, and also when the effective skill
is below the minimum of the rules (default 3), there is no roll and the result is a failure
(p. 2, and deviation 7). A Legal Adventure never asks for such a roll (see `CanTryRoll` in the spec). -/
def makeRollWith [Monad m] (rules : RuleSet) (roll : Nat → m (List Nat))
    (who : String) (target : RollTarget) (modifier : Int) (skill? : Option Int) :
    m (RollResult × Report) := do
  let some skill := skill?
    | return (.failure, .cannotTry who target modifier none)
  if skill < rules.minimumRollLevel then
    return (.failure, .cannotTry who target modifier (some skill))
  let r ← rollAgainstWith rules roll skill
  return (r.result, .successRoll who target modifier r)

/-- `makeRollWith` with the seeded dice. -/
def makeRoll (rules : RuleSet) (who : String) (target : RollTarget) (modifier : Int)
    (skill? : Option Int) : Roll (RollResult × Report) :=
  makeRollWith rules rollDice who target modifier skill?

/-- A being in a Fight, with its current HP and its last maneuver. -/
structure Fighter where
  being : Being
  hp : Int
  /-- The maneuver from the being's last turn. It sets the being's defense (p. 25).
  Before its first turn, a being counts as doing nothing, which defends like Attack. -/
  maneuver : Maneuver := .attack
  deriving DecidableEq

/-- A Fighter is alive while it has more than 0 HP (see deviation 1). -/
def Fighter.alive (f : Fighter) : Bool := f.hp > 0

/-- The Dodge score of a Fighter now, or `none` if it cannot defend.
Dodge is halved (rounded up) when the being has less than 1/3 of its HP left (p. 29),
if the rules say so. Then the bonus from the last maneuver is added. -/
def Fighter.dodge (rules : RuleSet) (f : Fighter) : Option Nat :=
  let d := rules.dodge f.being
  let base := if rules.halveDodgeBelowThird && 3 * f.hp < rules.maxHP f.being then (d + 1) / 2 else d
  f.maneuver.dodgeBonus.map (base + ·)

/-- A rule fires for its side when the stated combat condition holds. -/
def CombatRule.active (r : CombatRule) (rules : RuleSet) (actor : Actor)
    (self other : Fighter) : Bool :=
  r.forHero actor.isNone && match r.trigger with
  | "always" => true
  | "wounded" => 2 * self.hp ≤ rules.maxHP self.being
  | "desperate" => 3 * self.hp ≤ rules.maxHP self.being
  | "reckless" => self.maneuver == .allOutAttack
  | "guarding" => self.maneuver == .allOutDefense
  | "againstReckless" => other.maneuver == .allOutAttack
  | "againstGuarding" => other.maneuver == .allOutDefense
  | "againstFlame" => other.being.weapon == .flamethrower
  | _ => false

/-- The damage dice for a hit. After an attack roll of 3, every die counts as 6 and no dice
are rolled. Returns the faces and `true` if they are the maximum. -/
def damageFacesWith [Monad m] (roll : Nat → m (List Nat)) (count : Nat) (attackTotal : Nat) :
    m (List Nat × Bool) := do
  if attackTotal = 3 then return (List.replicate count 6, true)
  let faces ← roll count
  return (faces, false)

/-- One attack by `att` (actor `attId`) on `dfn` (actor `dfnId`), under `rules`, with the dice
from `roll`. The last maneuver of `att` gives the bonus to hit. Returns the injury done and the
Reports. The dice come in this order: 3 for the attack, then 3 for the Dodge unless the attack is
a critical success or the defender cannot defend, then the damage dice unless the attack roll is 3. -/
def attackWith [Monad m] (rules : RuleSet) (roll : Nat → m (List Nat))
    (attId : Actor) (att : Fighter) (dfnId : Actor) (dfn : Fighter) : m (Nat × List Report) := do
  let offense := rules.combatRules.filter fun r => r.active rules attId att dfn &&
    (r.hitBonus != 0 || r.damageBonus != 0)
  let defense := rules.combatRules.filter fun r => r.active rules dfnId dfn att && r.armorBonus > 0
  let effectReports := (offense ++ defense).map fun r => Report.worldRule r.name r.description
  let level := rules.weaponLevel att.being + att.maneuver.hitBonus + (offense.map (·.hitBonus)).sum
  if level < rules.minimumRollLevel then
    return (0, [.cannotAttack att.being.name level])
  let r ← rollAgainstWith rules roll level
  let line := Report.attack attId att.being.name dfnId dfn.being.name att.being.weapon
    ((rules.equipmentFor att.being).map (·.name)) r
  if !r.result.succeeded then
    return (0, effectReports ++ [line])
  let mut reports := effectReports ++ [line]
  if r.result != .criticalSuccess then
    match dfn.dodge rules with
    | none =>
      reports := reports ++ [.noDefense dfn.being.name]
    | some dodge =>
      let d ← rollAgainstWith rules roll dodge
      -- A defense roll has no critical results: it just succeeds or fails (p. 28).
      let dodged := d.result.succeeded
      reports := reports ++ [.dodge dfn.being.name { d with result := if dodged then .success else .failure }]
      if dodged then
        return (0, reports)
  let baseDice := rules.weaponDice att.being
  let dice := { baseDice with add := baseDice.add + (offense.map (·.damageBonus)).sum }
  let kind := att.being.weapon.damageType
  let (faces, maxed) ← damageFacesWith roll dice.count r.total
  let basic := rules.basicDamage dice kind faces.sum
  let dr := rules.dr dfn.being + (defense.map (·.armorBonus)).sum
  let inj := rules.injury kind dr basic
  let hpLeft := dfn.hp - inj
  reports := reports ++
    [.damage dfnId dfn.being.name faces maxed dice.add kind.name basic dr inj hpLeft]
  if dfn.alive && hpLeft ≤ 0 then
    reports := reports ++ [.falls dfnId dfn.being.name]
  return (inj, reports)

/-- One attack with the seeded dice. -/
def attack (rules : RuleSet) (attId : Actor) (att : Fighter) (dfnId : Actor) (dfn : Fighter) :
    Roll (Nat × List Report) :=
  attackWith rules rollDice attId att dfnId dfn

/-- The state of a Fight: the Character and the Creatures. -/
structure FightState where
  hero : Fighter
  foes : List Fighter
  deriving DecidableEq

/-- The Fight is over when the Character is dead or every Creature is dead. -/
def FightState.over (s : FightState) : Bool :=
  !s.hero.alive || s.foes.all (!·.alive)

/-- `true` if `a` acts before `b`: higher Basic Speed first, then higher DX.
The Bool is `true` for the Character. A tie that is left goes to the Character if the rules say so. -/
def actsBefore (rules : RuleSet) (a b : Being × Bool) : Bool :=
  if rules.speedX4 a.1 != rules.speedX4 b.1 then rules.speedX4 a.1 > rules.speedX4 b.1
  else if rules.attr a.1 .dx != rules.attr b.1 .dx then rules.attr a.1 .dx > rules.attr b.1 .dx
  else if rules.heroWinsInitiativeTies then a.2 else !a.2

/-- The turn order for a Fight. It is set at the start and does not change (p. 24). -/
def turnOrder (rules : RuleSet) (hero : Being) (foes : List Being) : List Actor :=
  let all : List (Actor × Being × Bool) :=
    (none, hero, true) :: (foes.zipIdx.map fun (b, i) => (some i, b, false))
  (all.mergeSort fun x y => actsBefore rules x.2 y.2).map (·.1)

/-- Change the HP of Creature number `i`. -/
def hurtFoe (foes : List Fighter) (i : Nat) (inj : Nat) : List Fighter :=
  foes.modify i fun f => { f with hp := f.hp - inj }

/-- A Report that says which maneuver a being chose. Attack needs no Report. -/
def announce (name : String) (m : Maneuver) : List Report :=
  if m = .attack then [] else [.maneuver name m]

/-- An attack function: attacker number, attacker, defender number, defender.
It returns the injury done and the Reports. -/
abbrev AttackFn (m : Type → Type) := Actor → Fighter → Actor → Fighter → m (Nat × List Report)

/-- A spray: `att` attacks each living Creature in list order, with separate rolls for each.
`i` is the number of the first Creature in `foes`. -/
def sprayWith [Monad m] (attackFn : AttackFn m) (att : Fighter) (i : Nat) :
    List Fighter → m (List Fighter × List Report)
  | [] => return ([], [])
  | foe :: rest => do
    let (hit, reports) ← if foe.alive then do
        let (inj, reports) ← attackFn none att (some i) foe
        pure ({ foe with hp := foe.hp - inj }, reports)
      else pure (foe, [])
    let (others, more) ← sprayWith attackFn att (i + 1) rest
    return (hit :: others, reports ++ more)

/-- The Character's turn. The Character uses maneuver `choice`. If the maneuver includes
an attack, the Character attacks Creature number `target`. With a spray weapon, the Character
attacks every living Creature, and `target` does not matter. Without a spray weapon, a dead or
missing target makes the turn do nothing. -/
def heroTurnWith [Monad m] (attackFn : AttackFn m) (s : FightState) (choice : Maneuver)
    (target : Nat) : m (FightState × List Report) := do
  if s.over then return (s, [])
  let hero := { s.hero with maneuver := choice }
  let intro := announce hero.being.name choice
  if !choice.attacks then return ({ s with hero := hero }, intro)
  if hero.being.weapon.spray then
    let (foes, reports) ← sprayWith attackFn hero 0 s.foes
    return ({ s with hero := hero, foes := foes }, intro ++ reports)
  let some foe := s.foes[target]? | return (s, [])
  if !foe.alive then return (s, [])
  let (inj, reports) ← attackFn none hero (some target) foe
  return ({ s with hero := hero, foes := hurtFoe s.foes target inj }, intro ++ reports)

/-- The turn of Creature number `i`. A Creature always chooses Attack and attacks the Character. -/
def foeTurnWith [Monad m] (attackFn : AttackFn m) (s : FightState) (i : Nat) :
    m (FightState × List Report) := do
  if s.over then return (s, [])
  let some foe := s.foes[i]? | return (s, [])
  if !foe.alive then return (s, [])
  let (inj, reports) ← attackFn (some i) foe none s.hero
  return ({ s with hero := { s.hero with hp := s.hero.hp - inj } }, reports)

/-- Run the turns of the Creatures in `actors`, in order. The Character in `actors` is skipped. -/
def foeTurnsWith [Monad m] (attackFn : AttackFn m) (s : FightState) :
    List Actor → m (FightState × List Report)
  | [] => return (s, [])
  | none :: rest => foeTurnsWith attackFn s rest
  | some i :: rest => do
    let (s, first) ← foeTurnWith attackFn s i
    let (s, later) ← foeTurnsWith attackFn s rest
    return (s, first ++ later)

/-- The Creatures that act before the Character in each round. -/
def beforeCharacter (order : List Actor) : List Actor :=
  order.takeWhile (· != none)

/-- The Creatures that act after the Character in each round. -/
def afterCharacter (order : List Actor) : List Actor :=
  (order.dropWhile (· != none)).drop 1

/-- Finish a round paused at the Character's turn. Earlier enemy turns are not repeated. -/
def remainingRoundWith [Monad m] (attackFn : AttackFn m)
    (pick : FightState → m (Maneuver × Nat)) (order : List Actor) (s : FightState) :
    m (FightState × List Report) := do
  if s.over then return (s, [])
  let (choice, target) ← pick s
  let (s, mine) ← heroTurnWith attackFn s choice target
  let (s, after) ← foeTurnsWith attackFn s (afterCharacter order)
  return (s, mine ++ after)

/-- One round of a Fight in turn order `order`: the Creatures before the Character, then the
Character, then the Creatures after it. On its turn, the Character uses `pick` to choose a
maneuver and a target. Play, the simulator, and the fairness model all use this order. -/
def roundWith [Monad m] (attackFn : AttackFn m) (pick : FightState → m (Maneuver × Nat))
    (order : List Actor) (s : FightState) : m (FightState × List Report) := do
  let (s, before) ← foeTurnsWith attackFn s (beforeCharacter order)
  let (s, mine) ← if s.over then pure (s, []) else do
    let (choice, target) ← pick s
    heroTurnWith attackFn s choice target
  let (s, after) ← foeTurnsWith attackFn s (afterCharacter order)
  return (s, before ++ mine ++ after)

/-- The Character's turn with the seeded dice. -/
def heroTurn (rules : RuleSet) (s : FightState) (choice : Maneuver) (target : Nat) :
    Roll (FightState × List Report) :=
  heroTurnWith (attack rules) s choice target

/-- A Creature's turn with the seeded dice. -/
def foeTurn (rules : RuleSet) (s : FightState) (i : Nat) : Roll (FightState × List Report) :=
  foeTurnWith (attack rules) s i

/-- The turns of the Creatures in `actors`, with the seeded dice. -/
def foeTurns (rules : RuleSet) (s : FightState) (actors : List Actor) :
    Roll (FightState × List Report) :=
  foeTurnsWith (attack rules) s actors

/-! ## Tests -/

/-- A test being with Dodge 9, 12 HP, and no armor. -/
private def testBeing : Being :=
  { name := "Test", st := 12, dx := 12, iq := 10, ht := 12,
    skills := [(.broadsword, 12)], weapon := .broadsword, armor := .none }

-- Dodge with each maneuver, at full HP and below 1/3 HP.
#guard ({ being := testBeing, hp := 12 } : Fighter).dodge {} == some 9
#guard ({ being := testBeing, hp := 12, maneuver := .allOutDefense } : Fighter).dodge {} == some 11
#guard ({ being := testBeing, hp := 3, maneuver := .allOutDefense } : Fighter).dodge {} == some 7
#guard ({ being := testBeing, hp := 12, maneuver := .allOutAttack } : Fighter).dodge {} == none

/-- A Fight between two test beings, with the Character's last maneuver set to `m`. -/
private def testFight (m : Maneuver) : FightState :=
  ⟨{ being := testBeing, hp := 12, maneuver := m }, [{ being := testBeing, hp := 12 }]⟩

-- Halved Dodge with no maneuver bonus: 9 halves to 5.
#guard ({ being := testBeing, hp := 3 } : Fighter).dodge {} == some 5

/-- `true` if the Report is a Dodge roll. -/
private def isDodge : Report → Bool
  | .dodge .. => true
  | _ => false

-- All-Out Defense: the Character does not attack, and the maneuver is stored.
#guard
  let (s, reports) := (heroTurn {} (testFight .attack) .allOutDefense 0).run' ⟨7⟩
  s.foes.map (·.hp) == [12] && s.hero.maneuver == .allOutDefense &&
    reports == [.maneuver "Test" .allOutDefense]

-- After an All-Out Attack, the Character never dodges, and for some seeds it is hit with no defense.
#guard
  let logs := (List.range 50).map fun seed =>
    ((foeTurn {} (testFight .allOutAttack) 0).run' ⟨seed.toUInt64⟩).2
  logs.all (·.all (!isDodge ·)) && logs.any (·.contains (.noDefense "Test"))

/-- The Character makes an All-Out Attack, then an Attack, then the Creature attacks. Returns the Creature's Reports. -/
private def attackAfterAllOut : Roll (List Report) := do
  let (s, _) ← heroTurn {} (testFight .attack) .allOutAttack 0
  let (s, _) ← foeTurn {} s 0
  let (s, _) ← heroTurn {} s .attack 0
  let (_, reports) ← foeTurn {} s 0
  return reports

-- An Attack after an All-Out Attack gives the defense back: for some seeds the Character dodges.
#guard (List.range 50).any fun seed =>
  (attackAfterAllOut.run' ⟨seed.toUInt64⟩).any isDodge

/-- The target number of the first attack roll in a list of Reports. -/
private def firstAttackTarget : List Report → Option Int
  | .attack _ _ _ _ _ _ r :: _ => some r.target
  | _ :: rest => firstAttackTarget rest
  | [] => none

-- All-Out Attack adds 4 to the attack roll: Broadsword-12 needs 16 or less.
#guard
  let (_, reports) := (heroTurn {} (testFight .attack) .allOutAttack 0).run' ⟨1⟩
  firstAttackTarget reports == some 16

-- Each roll Report carries the faces it rolled, and its total is their sum.
#guard (List.range 50).all fun seed =>
  let r := (rollAgainst {} 10).run' ⟨seed.toUInt64⟩
  r.faces.length == 3 && r.faces.all (fun f => 1 ≤ f && f ≤ 6) && r.total == r.faces.sum

/-- A test attack that always does 3 injury and writes no Reports. -/
private def threeInjury : AttackFn Id := fun _ _ _ _ => pure (3, [])

/-- A plain test being with weapon `w`, as a Fighter with `hp` HP. -/
private def testFighter (name : String) (w : Weapon) (hp : Int := 10) : Fighter :=
  let b : Being :=
    { name, st := 10, dx := 10, iq := 10, ht := 10, skills := [], weapon := w, armor := .none }
  { being := b, hp }

/-- The HP of the Creatures after the Character's Attack on two Creatures, at Creature `target`. -/
private def foeHPAfterHeroTurn (w : Weapon) (firstHP : Int) (target : Nat := 1) : List Int :=
  let s : FightState := ⟨testFighter "Hero" w, [testFighter "A" .punch firstHP, testFighter "B" .punch]⟩
  (Id.run (heroTurnWith threeInjury s .attack target)).1.foes.map (·.hp)

-- A spray weapon hurts every living Creature.
#guard foeHPAfterHeroTurn .flamethrower 10 == [7, 7]
-- A spray weapon skips a dead Creature.
#guard foeHPAfterHeroTurn .flamethrower 0 == [0, 7]
-- Any other weapon hurts only the target.
#guard foeHPAfterHeroTurn .broadsword 10 0 == [7, 10]

end Rpg
