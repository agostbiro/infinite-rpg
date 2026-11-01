import Rpg.Live

/-!
Reproducible initial-state fairness diagnostics over the configured initial choice window.
Compute every confidence interval, even after a failure. This executable does not
issue an admission certificate or change the production validation budget.
-/
open Rpg Rpg.Probability Lean

/-- Diagnostic path recording. Each sampled result and RNG state is checked against production. -/
def tracedTrajectory (a : AdventureDefinition) (roundLimit : Nat) :
    Nat → SceneId → Int → Nat → List SceneId → Roll (Simulation.Trace × List SceneId)
  | fuel, id, hp, turns, visited => do
    if hp ≤ 0 then return (⟨.dead, turns⟩, visited)
    let some scene := a.story.scene? id | return (⟨.invalid, turns⟩, visited)
    let seen := id :: visited
    if scene.choices.isEmpty then return (⟨.ended, turns⟩, seen)
    match fuel with
    | 0 => return (⟨.censored, turns+1⟩, seen)
    | fuel+1 =>
      let some choice := scene.choices[← Simulation.choose scene.choices.length]?
        | return (⟨.invalid, turns⟩, seen)
      match choice.outcome with
      | .goto next => tracedTrajectory a roundLimit fuel next hp (turns+1) seen
      | .roll target modifier yes no =>
        let level := (a.rules.rollLevel a.hero target).map (· + modifier)
        let (result, _) ← makeRoll a.rules a.hero.name target modifier level
        tracedTrajectory a roundLimit fuel (if result.succeeded then yes else no) hp (turns+1) seen
      | .fight foes next =>
        let state : FightState :=
          { hero := { being := a.hero, hp }, foes := foes.map fun foe => { being := foe, hp := a.rules.maxHP foe } }
        let result ← Simulation.fight a.rules Simulation.pickManeuver (turnOrder a.rules a.hero foes) roundLimit state
        match result with
        | none => return (⟨.censored, turns+1⟩, seen)
        | some state =>
          if !state.hero.alive then return (⟨.dead, turns+1⟩, seen)
          tracedTrajectory a roundLimit fuel next state.hero.hp (turns+1) seen

/-- Measure graph checks, all simulations, all intervals, and checked node coverage. -/
def main (args : List String) : IO UInt32 := do
  let some file := args.head? | throw (IO.userError "Usage: benchmark-fairness FILE SEED [GAMES=5000]")
  let some seed := args[1]?.bind String.toNat? | throw (IO.userError "Provide SEED")
  if seed ≥ 18446744073709551616 then throw (IO.userError "SEED must fit UInt64")
  let games := (args[2]?.bind String.toNat?).getD 5000
  if games == 0 then throw (IO.userError "GAMES must be positive")
  let sink ← IO.mkRef ""
  let start ← IO.monoNanosNow
  let text ← IO.FS.readFile file
  let .ok draft := Draft.parse text | throw (IO.userError "Invalid JSON")
  let .ok defn := draft.checked | throw (IO.userError s!"Illegal: {draft.errors}")
  let difficulty := (Difficulty.ofProfile draft.validationProfile).getD .easy
  let a := liveCandidate defn difficulty.profile
  let checked ← IO.monoNanosNow
  let counts := sampleCounts a seed games
  sink.set s!"{counts.games}:{counts.aborted}:{counts.trials}:{counts.deaths}"
  let simulated ← IO.monoNanosNow
  if counts.aborted || counts.games != games then throw (IO.userError "Incomplete fixed batch")
  let mut rows : Array Json := #[]
  let mut meetsAllBands := true
  for row in [:validationRows a.horizon a.policy] do
    let obs := counts.observation row
    let band := confidenceBand a.horizon row a.policy
    let iv := Confidence.confidenceInterval a.policy.testRisk obs.trials obs.deaths
    let status := intervalStatus band obs iv
    meetsAllBands := meetsAllBands && status == "accepted"
    rows := rows.push (json% { row: $(row), trials: $(obs.trials), deaths: $(obs.deaths),
      lower: $(toString iv.lower), upper: $(toString iv.upper),
      target: $(toString band.target), status: $(status) })
  sink.set (Json.arr rows).compress
  let calculated ← IO.monoNanosNow
  let ids := defn.story.scenes.map (·.id)
  let mut reached := Array.replicate ids.length 0
  let mut replayCounts : ValidationCounts :=
    ⟨Array.replicate (validationRows a.horizon a.policy) 0,
     Array.replicate (validationRows a.horizon a.policy) 0, 0, false⟩
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut endings := 0
  for _ in [:games] do
    let ((trace, visited), next) := (tracedTrajectory defn validationRoundLimit (a.horizon+1)
      defn.story.start (defn.rules.maxHP defn.hero) 0 []).run rng
    let (reference, referenceRng) := (Simulation.trajectory defn validationRoundLimit (a.horizon+1)
      defn.story.start (defn.rules.maxHP defn.hero) 0).run rng
    if trace != reference || next.state != referenceRng.state then
      throw (IO.userError "Coverage replay disagrees with the production simulator")
    rng := next
    if trace.finish == .ended then endings := endings+1
    replayCounts := ({ replayCounts with games := replayCounts.games+1 }).observeTrace a.horizon a.policy trace
    for id in visited.eraseDups do
      reached := reached.modify (ids.idxOf id) (· + 1)
  if replayCounts.trials != counts.trials || replayCounts.deaths != counts.deaths then
    throw (IO.userError "Replay counts disagree with production sampleCounts")
  sink.set s!"{reached}:{endings}"
  let done ← IO.monoNanosNow
  let coverage := (ids.zip reached.toList).map fun (id,n) => json% { scene: $(id), games: $(n) }
  IO.println (json% { title: $(draft.adventure.title), source: $(file), profile: $(difficulty.profile),
    difficulty: $(difficulty.key), seed: $(seed), games: $(counts.games), horizon: $(a.horizon),
    trials: $(counts.trials), deaths: $(counts.deaths), coverage: $(coverage),
    rows: $(rows), meetsAllBands: $(meetsAllBands), choicesCovered: $(a.horizon+1),
    productionValidationGames: $(validationGamesFor a.policy), certificateIssued: false,
    endedWithinWindow: $(endings), coverageReplayMatches: true,
    retention: $(toString a.policy.retention), shape: $(a.policy.shape),
    tolerance: $(toString a.policy.tolerance), confidenceRisk: $(toString a.policy.testRisk),
    legalityNs: $(checked-start), simulationNs: $(simulated-checked), statisticsNs: $(calculated-simulated), coverageNs: $(done-calculated),
    validationTotalNs: $(calculated-start), completeTotalNs: $(done-start) }).compress
  return 0
