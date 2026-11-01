import Rpg.WorldChangeTests

open Rpg Rpg.WorldChange Rpg.Probability Rpg.Probability.Confidence

/-- Run compiled checks for a live-change fixture without consuming the held-out validation seed.
The change is checked against the policy of the game it changes. -/
def main (args : List String) : IO UInt32 := do
  if args.contains "--tuning" then
    let heavy := { Tests.proposal with rules := [
      { Tests.fury with trigger := "againstFlame", hitBonus := 4, damageBonus := 6, armorBonus := 2 }, Tests.shelter] }
    let mut results : List Bool := []
    for quarters in [4, 2, 1, 3, 5, 6, 8, 12, 16] do
      match (heavy.tune quarters).prepare roadGame with
      | .error errs => IO.println s!"{quarters}/4: {errs}"
      | .ok p =>
        let counts := sampleCounts p.candidate 1 validationGames
        let ok := decide (ValidationAccepted p.candidate.horizon counts (attemptRisk 0) 0 p.candidate.policy)
        results := results ++ [ok]
        IO.println s!"{quarters}/4: {ok}; deaths={counts.deaths}"
    return if results.head? == some false && results.any id then 0 else 1
  let proposal := Tests.proposal
  let game := if args.contains "--fight" then fightGame else roadGame
  match proposal.prepare game with
  | .error errs =>
    for e in errs do IO.eprintln e
    return 1
  | .ok p =>
    let started ← IO.monoMsNow
    let counts := sampleCounts p.candidate 1 validationGames
    IO.println s!"Sampling: {(← IO.monoMsNow) - started} ms; deaths={counts.deaths}"
    let checking ← IO.monoMsNow
    let accepted := decide (ValidationAccepted p.candidate.horizon counts (attemptRisk 0) p.candidate.elapsed
      p.candidate.policy)
    IO.println s!"Intervals: {(← IO.monoMsNow) - checking} ms; accepted={accepted}"
    if args.contains "--timing" then return if accepted then 0 else 1
    let errors := failedRows p.candidate.horizon counts (attemptRisk 0) p.candidate.elapsed p.candidate.policy
    IO.println s!"Live change: {counts.games} games; elapsed={p.candidate.elapsed}; error allowance={attemptRisk 0}"
    for row in [:counts.trials.size] do
      let n := counts.trials[row]!
      let k := counts.deaths[row]!
      let iv := confidenceInterval (attemptRisk 0) n k
      IO.println s!"row {row}: {k}/{n}; [{iv.lower}, {iv.upper}]"
    for e in errors do IO.eprintln e
    return if accepted then 0 else 1
