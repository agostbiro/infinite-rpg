import Rpg.Probability.CombatCertificate
import Rpg.Probability.ContinuationCertificate

namespace Rpg.Probability.CombatCertificateTests

private def fighter (name : String) : Being :=
  {name, st := 1, dx := 10, iq := 10, ht := 10, skills := [(.broadsword,12)],
    weapon := .broadsword, armor := .none}

private def state : FightState :=
  {hero := {being := fighter "Hero", hp := 1}, foes := [{being := fighter "Foe", hp := 1}]}

private def order := turnOrder {} state.hero.being (state.foes.map (·.being))

-- The producer supplies a certificate for a real stochastic fight.
#guard (certifyFight {} order state).isSome

-- A finite-state fight where no attack can hit must fail termination certification.
private def noHits : RuleSet := {successRoll := fun _ _ => .failure}
#guard (certifyFight noHits order state).isNone

-- Forging a zero remaining-time budget is rejected independently of the solver.
#guard
  let (_, cache) := (solveCombatAnswer (fastRound {} order) state).run {}
  let forged : CombatWitness := ⟨cache.map fun _ a => {a with rounds := 0}⟩
  !decide (forged.Accepted {} order state)

-- A bogus answer with unchanged total mass must fail the transition equations.
#guard
  let (_, cache) := (solveCombatAnswer (fastRound {} order) state).run {}
  let forged : CombatWitness := ⟨cache.map fun _ a => {a with outcomes := pure (.won 1)}⟩
  !decide (forged.Accepted {} order state)

-- The fast Bool check rejects both forged witnesses too.
#guard
  let (_, cache) := (solveCombatAnswer (fastRound {} order) state).run {}
  !(CombatWitness.mk (cache.map fun _ a => {a with rounds := 0})).check {} order [state] &&
  !(CombatWitness.mk (cache.map fun _ a => {a with outcomes := pure (.won 1)})).check {} order [state]

/-- A test being with 4 HP that fights with a broadsword. -/
private def sturdy (name : String) : Being :=
  {name, st := 4, dx := 10, iq := 10, ht := 10, skills := [(.broadsword,12)],
    weapon := .broadsword, armor := .none}

/-- A Fight with two Creatures, with the Character's last maneuver `m`. -/
private def twoFoes (m : Maneuver) (hp : Int) : FightState :=
  {hero := {being := sturdy "Hero", hp, maneuver := m},
   foes := [{being := sturdy "A", hp := 4}, {being := sturdy "B", hp := 2}]}

/-- The turn order of `twoFoes`. -/
private def twoFoesOrder := turnOrder {} (sturdy "Hero") [sturdy "A", sturdy "B"]

-- Differential test: the fast round gives exactly the weights of the spec round.
#guard [Maneuver.attack, .allOutAttack, .allOutDefense].all fun m => [1, 2, 4].all fun hp =>
  decide ((fastRound {} twoFoesOrder (twoFoes m hp)).sameWeights
    (roundDistribution {} heroPolicy twoFoesOrder (twoFoes m hp)))

-- Differential test: the rest of a paused round gives exactly the weights of the spec version,
-- for each maneuver and HP of the Character, and when the Fight is already over.
#guard [Maneuver.attack, .allOutAttack, .allOutDefense].all fun m => [0, 1, 2, 4].all fun hp =>
  let f : FightPhase :=
    {scene := 0, choice := 0, onWin := 1, order := twoFoesOrder, round := 2, state := twoFoes m hp}
  decide ((fastRemaining {} f.order f.state).sameWeights (remainingDistribution {} f))

-- The fast attack gives exactly the injury weights of `attackDistribution`.
#guard [Maneuver.attack, .allOutAttack, .allOutDefense].all fun m =>
  let s := twoFoes m 1
  decide ((injuryDistribution {} none s.hero (some 0) (s.foes.headD s.hero)).sameWeights
    (Prod.fst <$> attackDistribution {} none s.hero (some 0) (s.foes.headD s.hero))) &&
  decide ((injuryDistribution {} (some 1) (s.foes.getD 1 s.hero) none s.hero).sameWeights
    (Prod.fst <$> attackDistribution {} (some 1) (s.foes.getD 1 s.hero) none s.hero))

-- The level-by-level solver gives the same answers as the recursive solver, on each state that
-- the recursive solver reaches, and its witness passes the check.
#guard
  let start := twoFoes .attack 4
  let byLevel := solveChecked {} twoFoesOrder (attackBounds {} start) [start]
  let recursive := ((solveCombatAnswer (fastRound {} twoFoesOrder) start).run {}).2
  0 < recursive.size &&
  recursive.toList.all (fun (s, a) => match byLevel[s]? with
    | some b => decide (a.outcomes.sameWeights b.outcomes) && a.rounds == b.rounds
    | none => false) &&
  (CombatWitness.mk byLevel).check {} twoFoesOrder [start]

-- A small budget rejects the two-Creature Fight, but an unlimited budget certifies it.
#guard (certifyFight {} twoFoesOrder (twoFoes .attack 4) {states := 3}).isNone
#guard (certifyFight {} twoFoesOrder (twoFoes .attack 4) SolveBudget.unlimited).isSome
/-- An unlimited budget with every limit at 0. -/
private def zeroLimits : SolveBudget :=
  {limited := false, states := 0, entries := 0, roundEntries := 0, batchEntries := 0, work := 0}

-- An unlimited budget ignores every limit, even limits of 0.
#guard (certifyFight {} twoFoesOrder (twoFoes .attack 4) zeroLimits).isSome
#guard !SolveBudget.unlimited.over 1000000000 1000000000 1000000000
-- The odds of the balance graph do not use a budget: they give the Fight's real exit law, with
-- no weight on `stalled`, and the same law as the default budget.
#guard
  let law := checkedCombat {} twoFoesOrder (twoFoes .attack 4)
  law.mass (· == .stalled) == 0 && law.mass (fun _ => true) == 1 &&
  match certifyFight {} twoFoesOrder (twoFoes .attack 4) with
  | some c => decide (law.sameWeights c.outcomes)
  | none => false

-- `checkedCombat` gives the same exit law as `solveCombat` on the spec round, on two-Creature
-- Fights with different maneuvers and HP. `solveCombat` is the old recursive solver, refactored
-- in this change; it is not the code of `main`.
#guard [(Maneuver.attack, 4), (.attack, 1), (.allOutAttack, 3), (.allOutDefense, 2)].all fun (m, hp) =>
  let start := twoFoes m hp
  let old := (solveCombat {} heroPolicy twoFoesOrder start).run' {}
  decide ((checkedCombat {} twoFoesOrder start).sameWeights old)

/-- Rules in which every attack hits and does 1 injury, unless the defender has 50 DR or more.
A guarding Character, and a wounded Creature, get 100 DR; a wounded Creature cannot attack. The
Creature acts first. -/
private def stuckRules : RuleSet :=
  {maxHP := fun _ => 2, dodge := fun _ => 0,
   speedX4 := fun b => if b.name = "Foe" then 40 else 20,
   successRoll := fun level _ => if level ≥ 5 then .success else .failure,
   injury := fun _ dr _ => if dr ≥ 50 then 0 else 1,
   combatRules := [
     {name := "Guard", description := "100 DR while guarding.", side := .hero,
      trigger := .guarding, armorBonus := 100},
     {name := "Shaken", description := "A wounded Creature cannot attack.", side := .foes,
      trigger := .wounded, hitBonus := -100, armorBonus := 100}]}

/-- A Character with 1 HP against a Creature with 2 HP. The Character's last maneuver is Attack. -/
private def stuckStart : FightState :=
  {hero := {being := fighter "Hero", hp := 1}, foes := [{being := fighter "Foe", hp := 2}]}

/-- The turn order of `stuckStart`. -/
private def stuckOrder := turnOrder stuckRules (fighter "Hero") [fighter "Foe"]

-- From the start, the Creature kills the Character before the Character acts. The same state
-- after All-Out Defense cannot be reached: there the Character survives and wounds the Creature,
-- and then no one can hurt the other. The check must not fail on that state.
#guard (certifyFight stuckRules stuckOrder stuckStart SolveBudget.unlimited).isSome
#guard (checkedCombat stuckRules stuckOrder stuckStart).mass (· == .died) == 1
#guard
  let guarded := {stuckStart with hero := {stuckStart.hero with maneuver := .allOutDefense}}
  (certifyFight stuckRules stuckOrder guarded SolveBudget.unlimited).isNone

-- `keepReachable` follows each round result, also one with weight 0, and drops a state that no
-- start reaches. Here `a` goes to `b` with weight 0, and `c` has an answer but no start reaches it.
#guard
  let a := stuckStart
  let b := {stuckStart with foes := [{being := fighter "Foe", hp := 1}]}
  let c := {stuckStart with hero := {stuckStart.hero with maneuver := .allOutDefense}}
  let answer : CombatAnswer := ⟨pure .died, 0⟩
  let cache : CombatCache := (({} : CombatCache).insert a answer |>.insert b answer).insert c answer
  let rounds : Std.HashMap FightState (Distribution FightState) :=
    (({} : Std.HashMap FightState (Distribution FightState)).insert a ⟨[(a, 1), (b, 0)]⟩
      |>.insert b ⟨[(b, 1)]⟩).insert c ⟨[(c, 1)]⟩
  let kept := keepReachable cache rounds [a] 4
  kept.size == 2 && kept.contains a && kept.contains b && !kept.contains c

-- Batches keep at most 2 items and a cost of at most 5, except for one item alone.
#guard batchesBy id 5 2 [1, 2, 3, 4, 10] == [[1, 2], [3], [4], [10]]

/-- A Fight in which the Character sprays four Creatures with a flamethrower. -/
private def sprayFour : FightState :=
  {hero := {being := {sturdy "Hero" with weapon := .flamethrower}, hp := 4},
   foes := ["A", "B", "C", "D"].map fun n => {being := sturdy n, hp := 4}}

/-- The turn order of `sprayFour`. -/
private def sprayFourOrder :=
  turnOrder {} sprayFour.hero.being (sprayFour.foes.map (·.being))

-- One round of this Fight is too large, so it is rejected before any round is computed.
#guard roundSizeBound sprayFourOrder (attackBounds {} sprayFour) sprayFour >
  ({} : SolveBudget).roundEntries
#guard (certifyFight {} sprayFourOrder sprayFour).isNone
/-- The spray Fight, paused at the Character's turn. -/
private def sprayFourPaused : FightPhase :=
  {scene := 0, choice := 0, onWin := 1, order := sprayFourOrder, round := 1, state := sprayFour}

-- A paused round of this Fight is rejected before it is computed.
#guard (certifyContinuation {} sprayFourPaused).isNone
-- The reason is the size of one round, and the message names the living Creatures.
#guard match checkContinuation {} sprayFourPaused with
  | .error e => e == .roundTooLarge &&
      (e.message sprayFourPaused).startsWith "The paused Fight against A, B, C and D is too large" &&
      ((e.message sprayFourPaused).splitOn "after the Fight ends").length == 2
  | .ok _ => false

/-- The first Fight, paused, under rules in which no attack can hit. -/
private def noHitsPaused : FightPhase :=
  {scene := 0, choice := 0, onWin := 1, order, round := 1, state}

-- A paused Fight that can go on forever fails the check, and the message says so.
#guard match checkContinuation noHits noHitsPaused with
  | .error e => e == .checkFailed &&
      (e.message noHitsPaused).startsWith "The paused Fight against Foe could not be checked"
  | .ok _ => false

-- Over the work limit, the solver gives up, and the reason is the budget, not a failed check.
/-- The two-Creature Fight, paused. -/
private def twoFoesPaused : FightPhase :=
  {sprayFourPaused with order := twoFoesOrder, state := twoFoes .attack 4}

#guard match checkContinuation {} twoFoesPaused {work := 1} with
  | .error e => e == .overBudget
  | .ok _ => false
-- An unlimited budget also ignores the round limit of the paused round.
#guard (checkContinuation {} twoFoesPaused zeroLimits).toOption.isSome
#guard (checkContinuation {} twoFoesPaused {roundEntries := 0}).toOption.isNone

/-- Rules in which every attack hits and does 1 injury, every Being has 1 HP, and the Character
acts first. -/
private def oneHitRules : RuleSet :=
  {maxHP := fun _ => 1, dodge := fun _ => 0,
   speedX4 := fun b => if b.name = "Hero" then 40 else 20,
   successRoll := fun level _ => if level ≥ 5 then .success else .failure,
   injury := fun _ _ _ => 1}

/-- A one-HP Character against a one-HP Creature, paused at the Character's turn. -/
private def oneHitPaused : FightPhase :=
  {sprayFourPaused with
    order := turnOrder oneHitRules (fighter "Hero") [fighter "Foe"],
    state := {hero := {being := fighter "Hero", hp := 1}, foes := [{being := fighter "Foe", hp := 1}]}}

-- Every result of the paused round ends the Fight, so the solver gets no live state.
#guard (fastRemaining oneHitRules oneHitPaused.order oneHitPaused.state).entries.all (·.1.over)
#guard (checkContinuation oneHitRules oneHitPaused).toOption.isSome
-- The paused round still counts against the work limit and the batch limit.
#guard match checkContinuation oneHitRules oneHitPaused {work := 0} with
  | .error e => e == .overBudget
  | .ok _ => false
#guard match checkContinuation oneHitRules oneHitPaused {batchEntries := 0} with
  | .error e => e == .roundTooLarge
  | .ok _ => false
-- The results of the paused round count against the memory limit.
#guard match checkContinuation oneHitRules oneHitPaused {entries := 0} with
  | .error e => e == .overBudget
  | .ok _ => false

-- The solver gives up when its starts alone are over the state limit: one live start is a group
-- of 3 states.
#guard (solveFight (fastRound {} order) [state] (fun _ => 1) {states := 2}).isEmpty
#guard !(solveFight (fastRound {} order) [state] (fun _ => 1) {states := 3}).isEmpty

/-- Rules in which every weapon rolls 400 damage dice. -/
private def manyDice : RuleSet := {damage := fun _ _ => {count := 400, add := 0}}

-- A Fight that has already ended gets an empty witness, without the solver or the attack bounds,
-- and its exit law is the certain result.
#guard match certifyFight manyDice order {state with hero := {state.hero with hp := 0}} with
  | some c => c.witness.entries.isEmpty && decide (c.outcomes.sameWeights (pure .died))
  | none => false

-- Names are joined as in plain English.
#guard joinNames ["A"] == "A" && joinNames ["A", "B"] == "A and B" &&
  joinNames ["A", "B", "C"] == "A, B and C"

/-- A Creature with ST 1 that punches. -/
private def puncher (name : String) : Being :=
  {name, st := 1, dx := 10, iq := 10, ht := 10, skills := [], weapon := .punch, armor := .none}

/-- A Fight in which the Character sprays four Creatures that punch. -/
private def sprayPunch : FightState :=
  {sprayFour with foes := ["A", "B", "C", "D"].map fun n => {being := puncher n, hp := 1}}

/-- The turn order of `sprayPunch`. -/
private def sprayPunchOrder :=
  turnOrder {} sprayPunch.hero.being (sprayPunch.foes.map (·.being))

-- With a limit of 1 million for one round, each round of the group is under it, but the three
-- rounds together are above the batch limit. The plan puts each round in its own batch, so no
-- batch is above it. With the default limit for one round, the Fight is rejected at once.
#guard
  let size := roundSizeBound sprayPunchOrder (attackBounds {} sprayPunch)
  let budget : SolveBudget := {roundEntries := 1000000}
  let bounds := (maneuverStates sprayPunch).map size
  bounds.all (· ≤ budget.roundEntries) && bounds.sum > budget.batchEntries &&
  match planRounds size budget [sprayPunch] with
  | some batches => batches.all fun b => (b.map Prod.snd).sum ≤ budget.batchEntries
  | none => false
#guard (planRounds (roundSizeBound sprayPunchOrder (attackBounds {} sprayPunch)) {}
  [sprayPunch]).isNone

/-- Rules in which a roll succeeds only on a total of 3. Few attacks hit, so the Fight is short to
solve, but its round bound is large. -/
private def rareHits : RuleSet := {successRoll := fun _ total => if total = 3 then .success else .failure}

-- The default budget rejects the spray Fight against four Creatures that punch: one round is
-- above `roundEntries`. The odds of the balance graph use no budget, so they still give the real
-- exit law, with no weight on `stalled`.
#guard roundSizeBound sprayPunchOrder (attackBounds rareHits sprayPunch) sprayPunch >
  ({} : SolveBudget).roundEntries
#guard (certifyFight rareHits sprayPunchOrder sprayPunch).isNone
#guard
  let law := checkedCombat rareHits sprayPunchOrder sprayPunch
  law.mass (· == .stalled) == 0 && law.mass (fun _ => true) == 1

/-- Rules in which the Character gets +4 armor while guarding. -/
private def guardArmor : RuleSet :=
  {combatRules := defaultCombatRules ++
    [{name := "Guard Armor", description := "Armor while guarding.", side := CombatSide.hero,
      trigger := CombatTrigger.guarding, armorBonus := 4}]}

/-- Rules in which the Character's flamethrower rolls 6 dice. -/
private def bigFlame : RuleSet :=
  {equipment := [EquipmentRule.mk "Hero" .flamethrower "Big flamethrower" 12 6 0]}

-- `maxInjuries` is an upper bound on the injury results of one real attack, for each HP and
-- maneuver of both Fighters, with and without the 6-die flamethrower.
#guard [({} : RuleSet), bigFlame, guardArmor].all fun rules =>
  let hero : Fighter := sprayFour.hero
  let foe : Fighter := sprayFour.foes.headD hero
  let heroBound := maxInjuries rules none hero 4 (some 0) foe 4
  let foeBound := maxInjuries rules (some 0) foe 4 none hero 4
  [Maneuver.attack, .allOutAttack, .allOutDefense].all fun m =>
    [Maneuver.attack, .allOutAttack, .allOutDefense].all fun n => [1, 2, 4].all fun hp =>
      let att := {hero with hp, maneuver := m}
      let dfn := {foe with hp, maneuver := n}
      (injuryDistribution rules none att (some 0) dfn).entries.length ≤ heroBound &&
        (injuryDistribution rules (some 0) dfn none att).entries.length ≤ foeBound

/-- `maxInjuries` as it was before `hpSamples`: it tries every HP from 1 to `attHP` and `dfnHP`.
The test below compares the two. -/
private def maxInjuriesEvery (rules : RuleSet) (a : Actor) (att : Fighter) (attHP : Nat)
    (b : Actor) (dfn : Fighter) (dfnHP : Nat) : Nat :=
  let add (seen : List (Int × Nat)) (i : Nat) (m : Maneuver) (j : Nat) (n : Maneuver) :=
    let t := injuryTerms rules a {att with hp := i + 1, maneuver := m} b
      {dfn with hp := j + 1, maneuver := n}
    if seen.contains t then seen else t :: seen
  let terms := (List.range attHP).foldl (fun seen i => maneuverMenu.foldl (fun seen m =>
    (List.range dfnHP).foldl (fun seen j => maneuverMenu.foldl (fun seen n =>
      add seen i m j n) seen) seen) seen) []
  terms.foldl (fun best (bonus, dr) => max best (injuryCount rules a att bonus dr)) 1

/-- Rules with an effect on each HP trigger and on each side: the Character gets +1 damage while
wounded and +2 while desperate, and a Creature gets +2 armor while desperate. -/
private def hpEffects : RuleSet :=
  {combatRules := defaultCombatRules ++
    [{name := "Rage", description := "Damage while wounded.", side := CombatSide.hero,
      trigger := CombatTrigger.wounded, damageBonus := 1},
     {name := "Fury", description := "Damage while desperate.", side := CombatSide.hero,
      trigger := CombatTrigger.desperate, damageBonus := 2},
     {name := "Shell", description := "Armor while desperate.", side := CombatSide.foes,
      trigger := CombatTrigger.desperate, armorBonus := 2}]}

-- `maxInjuries` gives the same bound as a search over every HP. This is so for full HP from 0 to
-- 12 (which moves the trigger thresholds), for HP limits below and above full HP, and for rules
-- with and without HP triggers.
#guard [({} : RuleSet), bigFlame, guardArmor, hpEffects].all fun base =>
  (List.range 13).all fun full => [0, 1, 3, 5, 8, 13].all fun limit =>
    let rules := {base with maxHP := fun _ => full}
    let hero : Fighter := sprayFour.hero
    let foe : Fighter := sprayFour.foes.headD hero
    maxInjuries rules none hero limit (some 0) foe limit ==
        maxInjuriesEvery rules none hero limit (some 0) foe limit &&
      maxInjuries rules (some 0) foe limit none hero limit ==
        maxInjuriesEvery rules (some 0) foe limit none hero limit

-- The test above can fail: with `hpEffects`, a desperate Character and a Character at full HP
-- give different damage bonuses, so a search at full HP only would miss some injuries.
#guard
  let rules := {hpEffects with maxHP := fun _ => 12}
  let foe : Fighter := sprayFour.foes.headD sprayFour.hero
  injuryTerms rules none {sprayFour.hero with hp := 1} (some 0) foe !=
    injuryTerms rules none {sprayFour.hero with hp := 12} (some 0) foe

/-- A Fight in which the Character sprays two Creatures that punch, one of them wounded. -/
private def sprayTwo (m : Maneuver) (hp : Int) : FightState :=
  {hero := {sprayFour.hero with hp, maneuver := m},
   foes := [{being := puncher "A", hp := 2}, {being := puncher "B", hp := 1}]}

/-- The turn order of `sprayTwo`. -/
private def sprayTwoOrder := turnOrder {} (sprayTwo .attack 4).hero.being [puncher "A", puncher "B"]

/-- The number of results of one real round from `s`, with no merging. -/
private def unmergedSize (rules : RuleSet) (order : List Actor) (s : FightState) : Nat :=
  (roundWith (fastAttack rules) heroPolicy order s).entries.length

-- `roundSizeBound` is at least the number of results of a real round with no merging. This is so
-- for each maneuver and HP of the Character, with and without guard armor, with one target or a
-- spray.
#guard [({} : RuleSet), guardArmor].all fun rules =>
  [Maneuver.attack, .allOutAttack, .allOutDefense].all fun m => [1, 2, 4].all fun hp =>
    [(twoFoesOrder, twoFoes m hp), (sprayTwoOrder, sprayTwo m hp)].all fun (order, s) =>
      unmergedSize rules order s ≤ roundSizeBound order (attackBounds rules s) s

-- With the 6-die flamethrower, the round against four Creatures is rejected at once.
#guard roundSizeBound sprayFourOrder (attackBounds bigFlame sprayFour) sprayFour >
  ({} : SolveBudget).roundEntries

/-- The same Fight, paused after the Character's All-Out Defense. -/
private def sprayFourGuarded : FightState :=
  {sprayFour with hero := {sprayFour.hero with maneuver := .allOutDefense}}

-- The bound does not depend on the maneuver before the round: an attack in the round drops the
-- guard armor, so the bound must count the Creatures' attacks without it.
#guard roundSizeBound sprayFourOrder (attackBounds guardArmor sprayFourGuarded) sprayFourGuarded ==
  roundSizeBound sprayFourOrder (attackBounds guardArmor sprayFour) sprayFour
#guard roundSizeBound sprayFourOrder (attackBounds guardArmor sprayFourGuarded) sprayFourGuarded >
  ({} : SolveBudget).roundEntries

-- Bad output is rejected: the fast round is not the round with no attacks at all.
#guard !decide ((fastRound {} twoFoesOrder (twoFoes .attack 4)).sameWeights
  (pure (twoFoes .attack 4)))

end Rpg.Probability.CombatCertificateTests
