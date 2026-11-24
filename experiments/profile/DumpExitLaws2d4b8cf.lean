import Rpg.Adventures.Lafayette.Confidence

/-!
# The baseline exit laws, at commit 2d4b8cf

This program is not built here. It is for a copy of commit `2d4b8cf`, before the fast combat
check existed. It wrote the files in `experiments/profile/exit-laws-2d4b8cf`. To run it again:

    git archive 2d4b8cf | tar -x -C OLD
    cp experiments/profile/DumpExitLaws2d4b8cf.lean OLD/DumpExitLaws.lean
    (add `[[lean_exe]] name = "dump-exit-laws" root = "DumpExitLaws"` to OLD/lakefile.toml)
    cd OLD && lake build dump-exit-laws && .lake/build/bin/dump-exit-laws OUT

It takes about 9 to 11 minutes. The text form is the same as `profile-combat --dump`.
-/
open Rpg Rpg.Probability

/-- A fixed text form of an exit law: results sorted, equal results merged, zero weights dropped. -/
def canonical (d : Distribution CombatResult) : String :=
  let key : CombatResult → Int := fun | .died => -1 | .stalled => -2 | .won hp => hp
  let merged := d.collect.entries.filter (·.2 != 0)
  let sorted := merged.mergeSort (fun a b => key a.1 ≤ key b.1)
  " ".intercalate (sorted.map fun (r, p) => s!"{key r}:{p}")

def main (args : List String) : IO Unit := do
  let dir := args.headD "exit-laws"
  IO.FS.createDirAll dir
  let d := Lafayette.barrenHillDefinition
  let rules := d.rules
  let hero := d.hero
  for (foes, i) in (encounterFoes d.story).zipIdx do
    let order := turnOrder rules hero foes
    -- The solver of commit 2d4b8cf, with one cache for all entry HPs, from high to low.
    let cache := (entryHPs rules hero).reverse.foldl (fun cache (hp : Nat) =>
      ((solveCombatAnswer rules heroPolicy order (fightStart rules hero hp foes)).run cache).2) []
    let w : CombatWitness := ⟨cache⟩
    let lines := (entryHPs rules hero).map fun (hp : Nat) =>
      s!"hp={hp} {canonical (w.answer (fightStart rules hero hp foes)).outcomes}"
    IO.FS.writeFile s!"{dir}/fight-{i}.txt" (String.intercalate "\n" (toString (foes.map (·.name)) :: lines) ++ "\n")
    IO.println s!"wrote fight-{i} {foes.map (·.name)}"
