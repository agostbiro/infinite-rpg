import Rpg.Adventures.Lafayette.Confidence
import Rpg.Probability.ContinuationCertificate

/-!
# Timings and baseline of the combat check

For each Fight of the built-in Adventure, this program times the solver (`solveFight`) and the
checker (`CombatWitness.check`) over all entry HPs.

* `--dump DIR` writes the exit laws of each Fight to `DIR/fight-N.txt`, in a fixed text form.
* `--compare [DIR]` reads files in that form and checks that the exit laws are the same. With no
  `DIR`, it uses `experiments/profile/exit-laws-2d4b8cf`. A missing file is an error.
  `experiments/profile/exit-laws-2d4b8cf` holds the exit laws that the solver of commit
  `2d4b8cf` gave, before this program's solver existed. It used the spec round
  (`roundDistribution`) and none of the new code.
* `--stress` merges two million entries, to check that the merge needs no deep stack.
* `--grenadiers N` checks a Fight against `N` Grenadiers, at all entry HPs and as a paused Fight
  in a live change. A Fight above the solver's budget (`SolveBudget`) is rejected. Add
  `--flamethrower` to give Lafayette a flamethrower, which attacks every Grenadier at once. Add
  `--st S` to give each Grenadier ST `S`, and so `S` HP. `--work W` runs only the solver, with a
  work limit of `W`.
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

/-- The value that follows `flag` in the arguments, if it is not another flag. -/
def argAfter (flag : String) : List String → Option String
  | f :: v :: rest => if f == flag && !v.startsWith "--" then some v else argAfter flag (v :: rest)
  | _ => none

/-- The fixtures that the solver of commit `2d4b8cf` made. -/
def baselineDir : String := "experiments/profile/exit-laws-2d4b8cf"

/-- The folder to compare with: the value after `--compare`, or the baseline if none is given. -/
def compareDir (args : List String) : Option String :=
  if args.contains "--compare" then some ((argAfter "--compare" args).getD baselineDir) else none

/-- Print the timings of each Fight, and dump or compare the exit laws if asked. Return 1 if a
check or a comparison fails. -/
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
  if let some n := (argAfter "--grenadiers" args).bind String.toNat? then
    let hero := if args.contains "--flamethrower" then {hero with weapon := .flamethrower} else hero
    let st := ((argAfter "--st" args).bind String.toNat?).getD (Lafayette.grenadier 1).st
    let foes := (List.range n).map fun i => {Lafayette.grenadier (i + 1) with st}
    let order := turnOrder rules hero foes
    if let some work := (argAfter "--work" args).bind String.toNat? then
      -- Try the solver with a different work limit, and stop.
      let starts := encounterStarts rules hero foes
      let bounds := attackBounds rules (fightStart rules hero 0 foes)
      let t ← IO.monoMsNow
      let cache := solveFight (fastRound rules order) starts (roundSizeBound order bounds) {work}
      IO.println s!"{n} Grenadiers, work limit {work}: states={cache.size} ms={(← IO.monoMsNow) - t}"
      return 0
    let t0 ← IO.monoMsNow
    let encounter := (certifyEncounter rules hero foes).isSome
    let t1 ← IO.monoMsNow
    IO.println s!"{n} Grenadiers, all entry HPs: certified={encounter} ms={t1 - t0}"
    (← IO.getStdout).flush
    let paused : FightPhase := ⟨0, 0, 1, order, 1, fightStart rules hero (rules.maxHP hero) foes⟩
    IO.println s!"  round bound at the start: {roundSizeBound order (attackBounds rules paused.state) paused.state}"
    (← IO.getStdout).flush
    -- Time only the call that a live change makes.
    let t2 ← IO.monoMsNow
    let continuation := (certifyContinuation rules paused).isSome
    IO.println s!"{n} Grenadiers, paused Fight: certified={continuation} ms={(← IO.monoMsNow) - t2}"
    return 0
  let mut totalSolve := 0
  let mut totalCheck := 0
  let mut allSame := true
  let mut allOk := true
  for (foes, i) in (encounterFoes d.story).zipIdx do
    let order := turnOrder rules hero foes
    let starts := encounterStarts rules hero foes
    let t0 ← IO.monoMsNow
    -- The same solver call as `certifyEncounter`, with the same round bounds.
    let bounds := attackBounds rules (fightStart rules hero 0 foes)
    let cache := solveChecked rules order bounds starts
    let size := cache.size
    let t1 ← IO.monoMsNow
    let w : CombatWitness := ⟨cache⟩
    let ok := w.check rules order starts
    let t2 ← IO.monoMsNow
    allOk := allOk && ok
    totalSolve := totalSolve + (t1 - t0)
    totalCheck := totalCheck + (t2 - t1)
    let largest := cache.fold (fun m s _ => max m (roundSizeBound order bounds s)) 0
    let work := cache.fold (fun m s _ => if s.over then m else m + roundSizeBound order bounds s) 0
    IO.println s!"{foes.map (·.name)} states={size} solve-ms={t1 - t0} check-ms={t2 - t1} ok={ok} max-digits={maxDigits cache} largest-round-bound={largest} work={work}"
    let text := lawsText rules hero foes w
    if let some dir := argAfter "--dump" args then
      IO.FS.createDirAll dir
      IO.FS.writeFile s!"{dir}/fight-{i}.txt" text
    if let some dir := compareDir args then
      let expected ← IO.FS.readFile s!"{dir}/fight-{i}.txt"
      let same := expected == text
      allSame := allSame && same
      IO.println s!"  same exit laws as {dir}/fight-{i}.txt at every entry HP: {same}"
    (← IO.getStdout).flush
  IO.println s!"total solve-ms={totalSolve} check-ms={totalCheck}"
  return if allSame && allOk then 0 else 1
