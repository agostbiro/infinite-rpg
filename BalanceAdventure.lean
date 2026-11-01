import Rpg.Balance

/-! Reproduce training and the one held-out validity test for a generated draft. -/
open Rpg Rpg.Probability Lean

/-- Balance a draft, test it once on the held-out seed, and save only an admitted draft. -/
def main (args : List String) : IO UInt32 := do
  let [file, difficulty, destination] := args
    | IO.eprintln "Usage: balance-adventure FILE easy|medium|hard OUTPUT"; return 2
  let some level := Difficulty.ofKey difficulty
    | IO.eprintln "Unknown difficulty"; return 2
  let .ok draft := Draft.parse (← IO.FS.readFile file)
    | IO.eprintln "Invalid JSON"; return 2
  let start ← IO.monoMsNow
  let tuned ← balanceDraft { draft with validationProfile := level.profile } fun i => do
    IO.eprintln s!"Training variant {i}/15"
    return true
  let balanced ← match tuned with
    | .ok d => pure d
    | .error errors => IO.eprintln ("\n".intercalate errors); return 1
  let trained ← IO.monoMsNow
  match balanced.toGame validationSeed with
  | .error errors => IO.eprintln ("\n".intercalate errors); return 1
  | .ok _ =>
    IO.FS.writeFile destination ((balanced.toJson.setObjVal! "fairnessSeed" (toJson validationSeed)).pretty ++ "\n")
    IO.println (json% { difficulty: $(difficulty), admitted: true,
      trainingMs: $(trained-start), totalMs: $((← IO.monoMsNow)-start) }).compress
    return 0
