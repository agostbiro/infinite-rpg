import Rpg.WorldChangePrompt
import Rpg.Catalog

/-! Exploratory policy comparisons and lifetime statistics use the actual compiled simulator.
The plan fixes seeds and sample counts before results are observed. No study result admits play. -/
open Rpg Rpg.Probability Rpg.Probability.Confidence Lean

/-- A labelled policy with meaningful Weibull parameters and a valid interval allowance. -/
structure StudyPolicy where
  name : String
  policy : BalancePolicy
  valid : policy.Valid
  delta : Rat
  deltaValid : 0 < delta ∧ delta < 1

/-- A legal game variant; deliberately unbalanced games remain eligible for measurement. -/
structure StudyVariant where
  name : String
  label : String
  candidate : StatisticalCandidate

/-- Turn histories retain deaths, successful endings, and all unresolved outcomes. -/
structure LifetimeCounts where
  deaths : Array Nat
  endings : Array Nat
  censored : Array Nat
  invalid : Nat := 0
  games : Nat := 0

/-- Convert a checked data error into a visible command failure. -/
def require (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

/-- Parse a natural number without accepting a missing value. -/
def readNat (text : String) : Except String Nat :=
  match text.toNat? with
  | some n => .ok n
  | none => .error s!"Invalid natural number: {text}"

/-- Read a nonnegative exact rational written as an integer or fraction. -/
def readRat (text : String) : Except String Rat := do
  match text.splitOn "/" with
  | [n] => return (← readNat n : Nat)
  | [n, d] =>
    let a ← readNat n
    let b ← readNat d
    if b = 0 then throw "Zero denominator in study plan"
    return (a : Rat) / (b : Rat)
  | _ => throw s!"Invalid rational: {text}"

/-- Parse and check all policy inputs before drawing any samples. -/
def readPolicy (j : Json) : Except String StudyPolicy := do
  let name ← j.getObjValAs? String "name"
  let q ← readRat (← j.getObjValAs? String "retention")
  let shape ← j.getObjValAs? Nat "shape"
  let tolerance ← readRat (← j.getObjValAs? String "tolerance")
  let delta ← readRat (← j.getObjValAs? String "delta")
  let policy : BalancePolicy := ⟨q, shape, tolerance⟩
  if hp : policy.Valid then
    if hd : 0 < delta ∧ delta < 1 then return ⟨name, policy, hp, delta, hd⟩
    else throw s!"Invalid confidence allowance: {name}"
  else throw s!"Invalid Weibull policy: {name}"

/-- All variants must pass the same character and adventure legality checker as play. -/
def makeVariant (name label : String) (rules : RuleSet) (hero : Being) (story : Adventure) :
    Except String StudyVariant :=
  if hc : checkCharacter rules hero = [] then
    if ha : check rules hero story = [] then
      .ok ⟨name, label, ⟨⟨rules, hero, checkCharacter_sound hc, story, check_sound ha⟩,
        liveHorizon, by decide, none, 0⟩⟩
    else .error s!"{name}: {check rules hero story}"
  else .error s!"{name}: {checkCharacter rules hero}"

/-- Fixed variants separate shared rules, story expansion, and deliberately bad balance. -/
def variants (original acorn : Draft) : Except String (List StudyVariant) := do
  let powerfulHero := { Lighthouse.mara with weapon := .flamethrower }
  let powerfulRules : RuleSet := {
    equipment := [⟨powerfulHero.name, .flamethrower, "Unchecked Sunfire", 18, 6, 6⟩] }
  let harshRules : RuleSet := {
    combatRules := defaultCombatRules ++ [{
      name := "Unbalanced Opposition", description := "Enemies always gain +4 to hit and +6 damage.",
      side := "foes", trigger := "always", hitBonus := 4, damageBonus := 6 }] }
  let peaceful := { Lighthouse.lighthouse with
    scenes := Lighthouse.lighthouse.scenes.map fun scene => { scene with
      choices := scene.choices.map fun choice => { choice with
        outcome := match choice.outcome with
          | .fight _ next => .goto next
          | other => other } } }
  return [
    ← makeVariant "original_lighthouse" "Original Lighthouse" { combatRules := [] } original.hero original.adventure,
    ← makeVariant "meta_rules_only" "Original story + new meta rules" {} original.hero original.adventure,
    ← makeVariant "expanded_lighthouse" "Expanded Lighthouse + meta rules" Lighthouse.rules Lighthouse.mara Lighthouse.lighthouse,
    ← makeVariant "unchecked_power" "Expanded Lighthouse: unchecked superweapon" powerfulRules powerfulHero Lighthouse.lighthouse,
    ← makeVariant "harsh_opposition" "Expanded Lighthouse: unbalanced enemies" harshRules Lighthouse.mara Lighthouse.lighthouse,
    ← makeVariant "peaceful_lighthouse" "Expanded Lighthouse: no combat" {} Lighthouse.mara peaceful,
    ← makeVariant "silver_acorn" "The Silver Acorn + meta rules" {} acorn.hero acorn.adventure]

/-- Full trajectories use the same choice policy, combat rules, and timeout handling as admission. -/
def lifetimes (a : AdventureDefinition) (seed games turnLimit : Nat) : LifetimeCounts := Id.run do
  let mut counts : LifetimeCounts := ⟨Array.replicate (turnLimit+2) 0,
    Array.replicate (turnLimit+2) 0, Array.replicate (turnLimit+2) 0, 0, 0⟩
  let mut rng : Rng := ⟨seed.toUInt64⟩
  for _ in [:games] do
    let (trace, next) := (Simulation.trajectory a validationRoundLimit turnLimit
      a.story.start (a.rules.maxHP a.hero) 0).run rng
    rng := next
    counts := { counts with games := counts.games + 1 }
    match trace.finish with
    | .dead => counts := { counts with deaths := counts.deaths.modify trace.turn (· + 1) }
    | .ended => counts := { counts with endings := counts.endings.modify trace.turn (· + 1) }
    | .censored => counts := { counts with censored := counts.censored.modify trace.turn (· + 1) }
    | .invalid => counts := { counts with invalid := counts.invalid + 1 }
  return counts

/-- Compare one fixed batch against one policy using the production admission predicate. -/
def policyResult (a : StatisticalCandidate) (counts : ValidationCounts) (p : StudyPolicy) : Json :=
  let rows := (List.finRange (a.horizon+1)).map fun i =>
    let band := confidenceBandsFor p.policy a.horizon i
    json% { row: $(i.val), target: $(toString band.target), tolerance: $(toString band.tolerance),
      trials: $((counts.observation i.val).trials), deaths: $((counts.observation i.val).deaths) }
  json% { name: $(p.name), retention: $(toString p.policy.retention), shape: $(p.policy.shape),
    tolerance: $(toString p.policy.tolerance), delta: $(toString p.delta),
    passed: $(decide (ValidationAccepted a.horizon counts p.delta 0 p.policy)), rows: $(rows) }

/-- Stream reproducible observations; startup validates the plan rather than silently changing it. -/
def main (args : List String) : IO Unit := do
  let plan ← require (Json.parse (← IO.FS.readFile "experiments/plan.json"))
  let policies ← require (listField plan "policies" readPolicy)
  let seeds ← require (plan.getObjValAs? (List Nat) "admission_seeds")
  let games ← require (plan.getObjValAs? Nat "lifetime_games_per_variant")
  let lifeSeed ← require (plan.getObjValAs? Nat "lifetime_seed")
  let turnLimit ← require (plan.getObjValAs? Nat "lifetime_turn_limit")
  if (← require (plan.getObjValAs? Nat "admission_games_per_batch")) != validationGames ||
      (← require (plan.getObjValAs? Nat "combat_round_limit")) != validationRoundLimit ||
      (← require (plan.getObjValAs? Nat "balance_horizon")) != liveHorizon then
    throw (IO.userError "The study plan disagrees with the shared admission parameters")
  let original ← require (Draft.parse (← IO.FS.readFile "experiments/adventures/lighthouse-original.json"))
  let acorn ← require (Draft.parse (← IO.FS.readFile "experiments/adventures/silver-acorn.json"))
  let cases ← require (variants original acorn)
  if (cases.map (·.name)) != (← require (plan.getObjValAs? (List String) "variants")) then
    throw (IO.userError "The planned variants differ from the compiled variants")
  if args.contains "--screen" then
    for v in cases do
      let counts := sampleCounts v.candidate 1 validationGames
      IO.println s!"{v.name}: {decide (ValidationAccepted liveHorizon counts)}; deaths={counts.deaths}"
    return
  let selected := (args.find? (·.startsWith "--variant=")).map (fun s => (s.drop 10).toString)
  if let some name := selected then
    if !(cases.any (·.name == name)) then throw (IO.userError s!"Unknown variant: {name}")
  for v in cases do
    if selected.isSome && selected != some v.name then continue
    IO.eprintln s!"Measuring {v.name}: {games} complete-game trajectories"
    let life := lifetimes v.candidate.toAdventureDefinition lifeSeed games turnLimit
    let mut batches : Array Json := #[]
    for seed in seeds do
      IO.eprintln s!"  fixed admission batch {seed}: {validationGames} games, {policies.length} policies"
      let counts := sampleCounts v.candidate seed validationGames
      let comparisons := policies.map (policyResult v.candidate counts)
      batches := batches.push (json% { seed: $(seed), games: $(counts.games), aborted: $(counts.aborted),
        trials: $(counts.trials), deaths: $(counts.deaths), policies: $(comparisons) })
    let result := json% { variant: $(v.name), label: $(v.label), lifeSeed: $(lifeSeed),
      turnLimit: $(turnLimit), rules: $(v.candidate.rules.combatRules.map WorldChange.ruleJson),
      lifetime: { games: $(life.games), deaths: $(life.deaths), endings: $(life.endings),
        censored: $(life.censored), invalid: $(life.invalid) }, batches: $(batches) }
    IO.println result.compress
    (← IO.getStdout).flush
