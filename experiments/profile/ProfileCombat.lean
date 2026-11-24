import Rpg.Adventures.Lafayette.Confidence

/-!
# Timings and baseline of the combat check

For each Fight of the built-in Adventure, this program times the solver (`solveFight`) and the
checker (`CombatWitness.check`) over all entry HPs.

* `--dump DIR` writes the exit laws of each Fight to `DIR/fight-N.txt`, in a fixed text form.
* `--compare DIR` reads files in that form and checks that the exit laws are the same.
  `experiments/profile/exit-laws-2d4b8cf` holds the exit laws that the solver of commit
  `2d4b8cf` gave, before this program's solver existed. It used the spec round
  (`roundDistribution`) and none of the new code.
* `--stress` merges two million entries, to check that the merge needs no deep stack.
-/

open Rpg Rpg.Probability

/-- The number of digits of the largest denominator in the answers. -/
def maxDigits (cache : CombatCache) : Nat :=
  cache.fold (fun m _ a => a.outcomes.entries.foldl (fun m e => max m (toString e.2.den).length) m) 0

/-- A fixed text form of an exit law: results sorted, equal results merged, zero weights dropped.
The dump program of the baseline uses the same form. -/
def canonical (d : Distribution CombatResult) : String :=
  let key : CombatResult → Int := fun | .died => -1 | .stalled => -2 | .won hp => hp
  let merged := d.collect.entries.filter (·.2 != 0)
  let sorted := merged.mergeSort (fun a b => key a.1 ≤ key b.1)
  " ".intercalate (sorted.map fun (r, p) => s!"{key r}:{p}")

/-- The text of the exit laws of one Fight: the names of the Creatures, then one line per entry HP. -/
def lawsText (rules : RuleSet) (hero : Being) (foes : List Being) (w : CombatWitness) : String :=
  let lines := (entryHPs rules hero).map fun (hp : Nat) =>
    s!"hp={hp} {canonical (w.answer (fightStart rules hero hp foes)).outcomes}"
  String.intercalate "\n" (toString (foes.map (·.name)) :: lines) ++ "\n"

/-- The value that follows `flag` in the arguments. -/
def argAfter (flag : String) : List String → Option String
  | f :: v :: rest => if f == flag then some v else argAfter flag (v :: rest)
  | _ => none

/-- Print the timings of each Fight, and dump or compare the exit laws if asked. -/
def main (args : List String) : IO UInt32 := do
  if args.contains "--stress" then
    -- Two million entries with distinct values: the merge must not use one stack frame each.
    let size := 2000000 + args.length
    let big : Distribution Nat := ⟨(List.range size).map fun i => (i, (1 : Rat))⟩
    let t ← IO.monoMsNow
    let merged := big.sortCollect id
    IO.println s!"stress: {merged.entries.length} entries merged in {(← IO.monoMsNow) - t} ms"
    return 0
  let d := Lafayette.barrenHillDefinition
  let rules := d.rules
  let hero := d.hero
  let mut totalSolve := 0
  let mut totalCheck := 0
  let mut allSame := true
  for (foes, i) in (encounterFoes d.story).zipIdx do
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
    let text := lawsText rules hero foes w
    if let some dir := argAfter "--dump" args then
      IO.FS.createDirAll dir
      IO.FS.writeFile s!"{dir}/fight-{i}.txt" text
    if let some dir := argAfter "--compare" args then
      let expected ← IO.FS.readFile s!"{dir}/fight-{i}.txt"
      let same := expected == text
      allSame := allSame && same
      IO.println s!"  same exit laws as {dir}/fight-{i}.txt at every entry HP: {same}"
    (← IO.getStdout).flush
  IO.println s!"total solve-ms={totalSolve} check-ms={totalCheck}"
  return if allSame then 0 else 1
