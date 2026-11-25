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

-- Batches keep at most 2 items and a cost of at most 5, except for one item alone.
#guard batchesBy id 5 2 [1, 2, 3, 4, 10] == [[1, 2], [3], [4], [10]]

/-- A Fight in which the Character sprays four Creatures with a flamethrower. -/
private def sprayFour : FightState :=
  {hero := {being := {sturdy "Hero" with weapon := .flamethrower}, hp := 4},
   foes := ["A", "B", "C", "D"].map fun n => {being := sturdy n, hp := 4}}

private def sprayFourOrder :=
  turnOrder {} sprayFour.hero.being (sprayFour.foes.map (·.being))

-- One round of this Fight is too large, so it is rejected before any round is computed.
#guard roundSizeBound sprayFourOrder (attackBounds {} sprayFour) sprayFour >
  ({} : SolveBudget).roundEntries
#guard (certifyFight {} sprayFourOrder sprayFour).isNone

/-- A Creature with ST 1 that punches. -/
private def puncher (name : String) : Being :=
  {name, st := 1, dx := 10, iq := 10, ht := 10, skills := [], weapon := .punch, armor := .none}

/-- A Fight in which the Character sprays four Creatures that punch. -/
private def sprayPunch : FightState :=
  {sprayFour with foes := ["A", "B", "C", "D"].map fun n => {being := puncher n, hp := 1}}

private def sprayPunchOrder :=
  turnOrder {} sprayPunch.hero.being (sprayPunch.foes.map (·.being))

-- Each round of the group is under the limit for one round, but the three rounds together are
-- above the batch limit. The plan puts each round in its own batch, so no batch is above it.
#guard
  let size := roundSizeBound sprayPunchOrder (attackBounds {} sprayPunch)
  let budget : SolveBudget := {}
  let bounds := (maneuverStates sprayPunch).map size
  bounds.all (· ≤ budget.roundEntries) && bounds.sum > budget.batchEntries &&
  match planRounds size budget [sprayPunch] with
  | some batches => batches.all fun b => (b.map Prod.snd).sum ≤ budget.batchEntries
  | none => false

/-- Rules in which the Character gets +4 armor while guarding. -/
private def guardArmor : RuleSet :=
  {combatRules := defaultCombatRules ++
    [{name := "Guard Armor", description := "Armor while guarding.", side := CombatSide.hero,
      trigger := CombatTrigger.guarding, armorBonus := 4}]}

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
