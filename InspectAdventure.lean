import Rpg.Live

/-! Run the existing statistical test over a requested finite window.
This diagnostic does not bypass admission or hide rows with no observations. -/
open Rpg Rpg.Probability Lean

/-- Read an unsigned option, or use its documented default. -/
def optionNat (args : List String) (key : String) (fallback : Nat) : Nat :=
  match args.dropWhile (· != key) with
  | _ :: value :: _ => value.toNat?.getD fallback
  | _ => fallback

/-- Validate a JSON adventure and print machine-readable counts, intervals and timings. -/
def main (args : List String) : IO UInt32 := do
  let some file := args.head? | IO.eprintln "Usage: inspect-adventure FILE [--horizon N] [--seed 20261103] [--summary]"; return 2
  let start ← IO.monoMsNow
  let text ← IO.FS.readFile file
  let .ok draft := Draft.parse text | IO.eprintln "Invalid adventure JSON"; return 2
  let .ok defn := draft.checked | IO.eprintln s!"Illegal adventure: {draft.errors}"; return 2
  let checked ← IO.monoMsNow
  let horizon := optionNat args "--horizon" (liveCandidate defn draft.validationProfile).horizon
  if positive : 0 < horizon then
    let policy := profilePolicy draft.validationProfile
    let candidate : StatisticalCandidate := { toAdventureDefinition := defn, horizon, horizonPositive := positive, policy }
    let seed := optionNat args "--seed" validationSeed
    let (counts, admitted) := admitWithSeed candidate seed
    let admittedFlag := admitted.isSome
    if args.contains "--summary" then
      let validated ← IO.monoMsNow
      IO.println (json% { title: $(draft.adventure.title), profile: $(draft.validationProfile),
        horizon: $(horizon), seed: $(seed), games: $(counts.games), aborted: $(counts.aborted),
        admitted: $(admittedFlag), trials: $(counts.trials), deaths: $(counts.deaths),
        legalityMs: $(checked-start), validationMs: $(validated-checked),
        totalMs: $(validated-start) }).compress
      return if admittedFlag then 0 else 1
    let perTurn := counts.deathsPerTurn policy
    let rows := (List.range (validationRows horizon policy)).map fun row =>
      let observation := counts.observation row
      let interval := Confidence.confidenceInterval policy.testRisk observation.trials observation.deaths
      let target := (confidenceBand horizon row policy).target
      let byTen := policy.protocol == .twoEventWindow && row == horizon+1
      let cumulative := if byTen then observation.deaths else
        ((List.range (row + 1)).map fun i => perTurn[i]!).foldl (· + ·) 0
      json% { row: $(row), turn: $(if byTen then 10 else if row = 0 then 1 else row + 1),
        kind: $(if byTen then "death-by-ten" else if row == 0 then "first-turn" else "conditional"),
        trials: $(observation.trials), deaths: $(observation.deaths),
        cumulativeDeaths: $(cumulative),
        lower: $(toString interval.lower), upper: $(toString interval.upper), target: $(toString target),
        status: $(intervalStatus (confidenceBand horizon row policy) observation interval) }
    let deathsByTen := if policy.protocol == .twoEventWindow then counts.deaths[horizon+1]!
      else ((List.range (min 10 (horizon + 1))).map fun i => perTurn[i]!).foldl (· + ·) 0
    let tenInterval := Confidence.confidenceInterval policy.testRisk counts.games deathsByTen
    let validated ← IO.monoMsNow
    IO.println (json% { title: $(draft.adventure.title), scenes: $(draft.adventure.scenes.length),
      horizon: $(horizon), turnsCovered: $(horizon + 1), seed: $(seed), games: $(counts.games),
      aborted: $(counts.aborted), admitted: $(admittedFlag), rows: $(rows),
      deathByTen: $(if horizon >= 9 || policy.protocol == .twoEventWindow then json% { deaths: $(deathsByTen), trials: $(counts.games),
        lower: $(toString tenInterval.lower), upper: $(toString tenInterval.upper) } else Json.null),
      profile: $(draft.validationProfile),
      metric: $(if policy.protocol == .twoEventWindow then "death-within-next-two-events" else "legacy-death-at-second-event"),
      confidence: $(toString (1 - policy.testRisk)), tolerance: $(toString policy.tolerance), errors: $(failedRows horizon counts policy), legalityMs: $(checked - start),
      validationMs: $(validated - checked), totalMs: $(validated - start) }).compress
    return if admittedFlag then 0 else 1
  else
    IO.eprintln "The horizon must be positive."
    return 2
