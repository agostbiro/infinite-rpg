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
  let some file := args.head? | IO.eprintln "Usage: inspect-adventure FILE [--horizon 29] [--seed 20261103]"; return 2
  let start ← IO.monoMsNow
  let text ← IO.FS.readFile file
  let .ok draft := Draft.parse text | IO.eprintln "Invalid adventure JSON"; return 2
  let .ok defn := draft.checked | IO.eprintln s!"Illegal adventure: {draft.errors}"; return 2
  let checked ← IO.monoMsNow
  let horizon := optionNat args "--horizon" 29
  if positive : 0 < horizon then
    let policy := profilePolicy draft.validationProfile
    let candidate : StatisticalCandidate := { toAdventureDefinition := defn, horizon, horizonPositive := positive, policy }
    let seed := optionNat args "--seed" validationSeed
    let (counts, admitted) := admitWithSeed candidate seed
    let admittedFlag := admitted.isSome
    let rows := (List.range (horizon + 1)).map fun row =>
      let observation := counts.observation row
      let interval := Confidence.confidenceInterval Confidence.confidenceDelta observation.trials observation.deaths
      let target := if row = 0 then 1 - policy.survival 1 else policy.deathAtTwo (row - 1)
      let cumulative := ((List.range (row + 1)).map fun i => counts.deaths[i]!).foldl (· + ·) 0
      json% { row: $(row), turn: $(if row = 0 then 1 else row + 1),
        trials: $(observation.trials), deaths: $(observation.deaths),
        cumulativeDeaths: $(cumulative),
        lower: $(toString interval.lower), upper: $(toString interval.upper), target: $(toString target) }
    let deathsByTen := ((List.range (min 10 (horizon + 1))).map fun i => counts.deaths[i]!).foldl (· + ·) 0
    let tenInterval := Confidence.confidenceInterval Confidence.confidenceDelta counts.games deathsByTen
    let validated ← IO.monoMsNow
    IO.println (json% { title: $(draft.adventure.title), scenes: $(draft.adventure.scenes.length),
      horizon: $(horizon), turnsCovered: $(horizon + 1), seed: $(seed), games: $(counts.games),
      aborted: $(counts.aborted), admitted: $(admittedFlag), rows: $(rows),
      deathByTen: $(if horizon >= 9 then json% { deaths: $(deathsByTen), trials: $(counts.games),
        lower: $(toString tenInterval.lower), upper: $(toString tenInterval.upper) } else Json.null),
      profile: $(draft.validationProfile), errors: $(failedRows horizon counts policy), legalityMs: $(checked - start),
      validationMs: $(validated - checked), totalMs: $(validated - start) }).compress
    return if admittedFlag then 0 else 1
  else
    IO.eprintln "The horizon must be positive."
    return 2
