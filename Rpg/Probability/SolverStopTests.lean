import Rpg.Probability.AdventureCertificate
import Rpg.Probability.ContinuationCertificate

/-!
# The solver does not stop early

Two loops of the solver have a fixed number of steps: the passes that find the states of a Fight
(`solveFightReport`), and the fuel of `keepReachable`. Comments argue that both are enough, and no
proof says so. If one ran out, the check would fail, and `checkedCombat` would give the whole
Fight `stalled`, with no warning.

So the solver says why it stopped (`SolveStop`). The tests below solve many small Fights with no
budget, as `checkedCombat` does, and check that the solver always finishes. They also check that
the solver reports a stop at the pass limit when a round leaves a group without HP loss, and that
a stalemate is a failed check, not a stop at a limit.
-/

namespace Rpg.Probability.SolverStopTests

/-- A Being with ST 10 and the weapon `w`, with skill 12 in it. -/
private def being (name : String) (w : Weapon) : Being :=
  {name, st := 10, dx := 10, iq := 10, ht := 10, skills := [(w.skill, 12)], weapon := w,
   armor := .none}

/-- The default rules, with `heroHP` full HP for the Character and `foeHP` for each Creature. -/
private def hpRules (heroHP foeHP : Nat) : RuleSet :=
  {maxHP := fun b => if b.name = "Hero" then heroHP else foeHP}

/-- Combat rules with an effect on each kind of trigger: HP, maneuvers, and both sides. -/
private def triggerEffects : List CombatRule :=
  [{name := "Rage", description := "Damage while wounded.", side := .hero, trigger := .wounded,
    damageBonus := 1},
   {name := "Shell", description := "Armor while desperate.", side := .foes,
    trigger := .desperate, armorBonus := 2},
   {name := "Feint", description := "Hit against a guard.", side := .foes,
    trigger := .againstGuarding, hitBonus := -1},
   {name := "Fury", description := "Damage when reckless.", side := .hero, trigger := .reckless,
    damageBonus := 1}]

/-- Combat rules that can make a stalemate. A guarding Character gets 100 DR. A wounded Creature
cannot attack, and gets 100 DR. -/
private def stalemateEffects : List CombatRule :=
  [{name := "Guard", description := "100 DR while guarding.", side := .hero, trigger := .guarding,
    armorBonus := 100},
   {name := "Shaken", description := "A wounded Creature cannot attack.", side := .foes,
    trigger := .wounded, hitBonus := -100, armorBonus := 100}]

/-- Four rule sets with the given full HP: the default rules, rules with trigger effects, rules
that can make a stalemate, and rules in which a roll succeeds only on 6 or less. -/
private def ruleSets (heroHP foeHP : Nat) : List RuleSet :=
  let base := hpRules heroHP foeHP
  [base,
   {base with combatRules := defaultCombatRules ++ triggerEffects},
   {base with combatRules := defaultCombatRules ++ stalemateEffects},
   {base with successRoll := fun _ total => if total ≤ 6 then .success else .failure}]

/-- Why the solver stops on the Fight of `hero` against `foes` at every entry HP. It is the solver
call of `certifyEncounter`, but with no budget, as in `checkedCombat`. -/
private def stopWithoutBudget (rules : RuleSet) (hero : Being) (foes : List Being) : SolveStop :=
  let start := fightStart rules hero 0 foes
  (solveCheckedReport rules (turnOrder rules hero foes) (attackBounds rules start)
    (encounterStarts rules hero foes) SolveBudget.unlimited).stop

/-- Fights against one Creature: each weapon of the Character, three weapons of the Creature, two
sizes, and the four rule sets. -/
private def oneFoeFights : List (RuleSet × Being × List Being) :=
  Weapon.all.flatMap fun w => [Weapon.largeKnife, .punch, .broadsword].flatMap fun v =>
    [(3, 2), (5, 3)].flatMap fun (heroHP, foeHP) => (ruleSets heroHP foeHP).map fun rules =>
      (rules, being "Hero" w, [being "Foe" v])

/-- Fights against two Creatures with 1 HP each: three weapons of the Character, two pairs of
Creatures, and two rule sets. -/
private def twoFoeFights : List (RuleSet × Being × List Being) :=
  [Weapon.broadsword, .punch, .flamethrower].flatMap fun w =>
    [[Weapon.largeKnife, .largeKnife], [.punch, .broadsword]].flatMap fun vs =>
      ((ruleSets 2 1).take 2).map fun rules =>
        (rules, being "Hero" w, vs.zipIdx.map fun (v, i) => being s!"Foe {i}" v)

#guard oneFoeFights.length == 120 && twoFoeFights.length == 12

-- With no budget, the solver finishes on each Fight against one Creature, at every entry HP. It
-- does not run out of passes or of fuel.
#guard oneFoeFights.all fun (rules, hero, foes) => stopWithoutBudget rules hero foes == .finished

-- The same for each Fight against two Creatures.
#guard twoFoeFights.all fun (rules, hero, foes) => stopWithoutBudget rules hero foes == .finished

-- The same for a Fight against three Creatures with 1 HP each.
#guard stopWithoutBudget (hpRules 2 1) (being "Hero" .broadsword)
  ([Weapon.largeKnife, .punch, .broadsword].zipIdx.map fun (v, i) => being s!"Foe {i}" v) ==
    .finished

-- The paused check of each Fight against two Creatures, at the Character's first turn, does not
-- report a stop at a limit of the solver either.
#guard twoFoeFights.all fun (rules, hero, foes) =>
  let order := turnOrder rules hero foes
  let paused : FightPhase :=
    ⟨0, 0, 1, order, 1, fightStart rules hero (rules.maxHP hero) foes⟩
  match checkContinuation rules paused with
  | .error .solverCutoff => false
  | _ => true

/-- The Fight of the stalemate test: a Character with 3 HP against a Creature with 2 HP, under
`stalemateEffects`. Both punch. A punch can do 1 injury, so it can leave the Creature wounded and
alive. -/
private def stalemateFight : RuleSet × Being × List Being :=
  ({hpRules 3 2 with combatRules := defaultCombatRules ++ stalemateEffects},
   being "Hero" .punch, [being "Foe" .punch])

-- A stalemate is not a stop at a limit. The solver finishes, and the check fails: a wounded
-- Creature cannot attack, and the Character cannot hurt it.
#guard
  let (rules, hero, foes) := stalemateFight
  stopWithoutBudget rules hero foes == .finished &&
    (certifyEncounter rules hero foes).isNone

/-- A round that never takes HP: each round adds 1 to the ST of each Creature, and the round after
ST 30 kills the Character. ST is not HP, so each round goes to a new group with no HP loss. -/
private def creepingRound (s : FightState) : Distribution FightState :=
  if s.foes.all (·.being.st < 30) then
    pure {s with foes := s.foes.map fun f => {f with being := {f.being with st := f.being.st + 1}}}
  else pure {s with hero := {s.hero with hp := 0}}

/-- The start of the creeping Fight: 1 HP on each side, and a Creature with ST 1. -/
private def creepingStart : FightState :=
  {hero := {being := being "Hero" .broadsword, hp := 1},
   foes := [{being := {being "Foe" .punch with st := 1}, hp := 1}]}

-- The solver reports a stop at the pass limit, not a budget limit, and gives no answers. The
-- passes are enough only when each new group has less HP, and this round breaks that.
#guard
  let report := solveFightReport creepingRound [creepingStart] (fun _ => 1) SolveBudget.unlimited
  report.stop == .outOfPasses && report.cache.isEmpty

-- A Fight over the budget reports `overBudget`: four Creatures sprayed by a flamethrower make a
-- round too large for the default budget.
#guard
  let foes := (List.range 4).map fun i => being s!"Foe {i}" .punch
  let rules := hpRules 4 4
  let hero := being "Hero" .flamethrower
  let start := fightStart rules hero 4 foes
  (solveCheckedReport rules (turnOrder rules hero foes) (attackBounds rules start) [start]).stop ==
    .overBudget

end Rpg.Probability.SolverStopTests
