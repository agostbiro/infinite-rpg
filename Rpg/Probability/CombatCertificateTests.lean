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
  let (_, cache) := (solveCombatAnswer {} heroPolicy order state).run []
  let forged : CombatWitness := ⟨cache.map fun (s,a) => (s, {a with rounds := 0})⟩
  !decide (forged.Accepted {} order state)

-- A bogus answer with unchanged total mass must fail the transition equations.
#guard
  let (_, cache) := (solveCombatAnswer {} heroPolicy order state).run []
  let forged : CombatWitness := ⟨cache.map fun (s,a) => (s, {a with outcomes := pure (.won 1)})⟩
  !decide (forged.Accepted {} order state)

end Rpg.Probability.CombatCertificateTests
