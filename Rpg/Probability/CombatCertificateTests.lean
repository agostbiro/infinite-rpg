import Rpg.Probability.CombatCertificate

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

-- The fast attack gives exactly the injury weights of `attackDistribution`.
#guard [Maneuver.attack, .allOutAttack, .allOutDefense].all fun m =>
  let s := twoFoes m 1
  decide ((injuryDistribution {} none s.hero (some 0) (s.foes.headD s.hero)).sameWeights
    (Prod.fst <$> attackDistribution {} none s.hero (some 0) (s.foes.headD s.hero))) &&
  decide ((injuryDistribution {} (some 1) (s.foes.getD 1 s.hero) none s.hero).sameWeights
    (Prod.fst <$> attackDistribution {} (some 1) (s.foes.getD 1 s.hero) none s.hero))

-- Bad output is rejected: the fast round is not the round with no attacks at all.
#guard !decide ((fastRound {} twoFoesOrder (twoFoes .attack 4)).sameWeights
  (pure (twoFoes .attack 4)))

end Rpg.Probability.CombatCertificateTests
