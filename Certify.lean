import Rpg.Adventures.Lafayette.Confidence

/-!
# Combat check of the built-in Adventure

This program admits the built-in Adventure, Lafayette at Barren Hill, and then runs the slow
combat check on it (`Probability.certify`). The check solves each Fight at each starting HP and
checks the result. It can take a long time, so the server does not run it at start-up.
-/

open Rpg Rpg.Probability

/-- Admit the built-in Adventure, then run the combat check. Returns 0 if both pass. -/
def main : IO UInt32 := do
  IO.println "BUILT-IN ADVENTURE (LAFAYETTE AT BARREN HILL): COMBAT CHECK"
  let (_, admitted) := admitStatistically Lafayette.statisticalCandidate
  let some a := admitted
    | IO.println "NOT ADMITTED: run `make validate` to see which rows failed."
      return 1
  IO.println "Admitted. The combat check runs now. It can take a long time."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let certified := certify a
  IO.println s!"elapsed-ms={(← IO.monoMsNow) - start}"
  if certified.isSome then
    IO.println "CERTIFIED: each Fight ends with probability one, at each starting HP."
    return 0
  IO.println "NOT CERTIFIED: a Fight failed the combat check."
  return 1
