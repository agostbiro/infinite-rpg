import Rpg.Adventures.Lafayette.Confidence

/-!
# Combat check of the built-in Adventure

This program admits the built-in Adventure, Lafayette at Barren Hill, and then runs the combat
check on it (`Probability.certify`). The check solves each Fight at each starting HP and checks
the result. Then it prints the exit law of each Fight at full HP: the chance of death, and the
mean HP left after a win. The server does not run this check yet.
-/

open Rpg Rpg.Probability

/-- A chance as a percent with one decimal, such as "12.3%". -/
def percent (r : Rat) : String :=
  let tenths := (r * 1000 + 1/2).floor
  s!"{tenths / 10}.{tenths % 10}%"

/-- The mean HP left after a win, as a number with one decimal. -/
def meanHPLeft (law : Distribution CombatResult) : String :=
  let won := law.mass fun | .won _ => true | _ => false
  let hp := law.expect fun | .won hp => (hp : Rat) | _ => 0
  if won = 0 then "-" else
  let tenths := (hp / won * 10 + 1/2).floor
  s!"{tenths / 10}.{tenths % 10}"

/-- Admit the built-in Adventure, then run the combat check. Returns 0 if both pass. -/
def main : IO UInt32 := do
  IO.println "BUILT-IN ADVENTURE (LAFAYETTE AT BARREN HILL): COMBAT CHECK"
  let (_, admitted) := admitStatistically Lafayette.statisticalCandidate
  let some a := admitted
    | IO.println "NOT ADMITTED: run `make validate` to see which rows failed."
      return 1
  IO.println "Admitted. The combat check runs now."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let some certified := certify a
    | IO.println s!"elapsed-ms={(← IO.monoMsNow) - start}"
      IO.println "NOT CERTIFIED: a Fight failed the combat check."
      return 1
  IO.println s!"elapsed-ms={(← IO.monoMsNow) - start}"
  IO.println "CERTIFIED: each Fight ends with probability one, at each starting HP."
  let d := certified.admitted.candidate.toAdventureDefinition
  let full := d.rules.maxHP d.hero
  IO.println s!"Exit laws at full HP ({full}):"
  for ⟨foes, hf⟩ in (encounterFoes d.story).attach do
    let law := certified.combat.exitLaw foes hf full (Nat.le_refl _)
    IO.println s!"  {foes.map (·.name)}: death {percent (law.mass (· == .died))}, mean HP left after a win {meanHPLeft law}"
  return 0
