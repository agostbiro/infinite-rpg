import Rpg.Adventures.Lafayette.Confidence

/-!
# Timings of the combat check

For each Fight of the built-in Adventure, this program times the solver (`solveFight`) and the
checker (`CombatWitness.check`) over all entry HPs. With `--compare`, it also solves each Fight
with one Creature with the old solver on the spec round (`combatDistribution`), and checks that
the exit laws are the same at every entry HP. The old solver takes seconds for each such Fight.
-/

open Rpg Rpg.Probability

/-- The number of digits of the largest denominator in the answers. -/
def maxDigits (cache : CombatCache) : Nat :=
  cache.fold (fun m _ a => a.outcomes.entries.foldl (fun m e => max m (toString e.2.den).length) m) 0

/-- Print the timings of each Fight. With `--compare`, also compare with the old solver. -/
def main (args : List String) : IO Unit := do
  let d := Lafayette.barrenHillDefinition
  let rules := d.rules
  let hero := d.hero
  let mut totalSolve := 0
  let mut totalCheck := 0
  for foes in encounterFoes d.story do
    let order := turnOrder rules hero foes
    let starts := encounterStarts rules hero foes
    let t0 ← IO.monoMsNow
    let cache := solveFight (fastRound rules order) starts
    let size := cache.size
    let t1 ← IO.monoMsNow
    let w : CombatWitness := ⟨cache⟩
    let ok := w.check rules order starts
    let t2 ← IO.monoMsNow
    totalSolve := totalSolve + (t1 - t0)
    totalCheck := totalCheck + (t2 - t1)
    IO.println s!"{foes.map (·.name)} states={size} solve-ms={t1 - t0} check-ms={t2 - t1} ok={ok} max-digits={maxDigits cache}"
    if args.contains "--compare" && foes.length == 1 then
      let same := (entryHPs rules hero).all fun hp =>
        let fast := (w.answer (fightStart rules hero hp foes)).outcomes
        let old := combatDistribution rules hero hp foes
        decide (fast.sameWeights old)
      IO.println s!"  same exit laws as the old solver at every entry HP: {same}"
    (← IO.getStdout).flush
  IO.println s!"total solve-ms={totalSolve} check-ms={totalCheck}"
