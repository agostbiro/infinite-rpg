import Rpg.Adventures.Illegal

/-!
# Cheats demo

This program prints each cheating Adventure in `Rpg.Lighthouse.Tests.cheats` with the errors the checker finds,
then The Drowned Lighthouse, which has no errors. It reads no input.
-/

open Rpg Rpg.Lighthouse

/-- Break text into lines of at most `width` characters. -/
def wrap (width : Nat) (text : String) : List String :=
  let words := text.splitOn " "
  let (lines, cur) := words.foldl (init := ([], "")) fun (lines, cur) w =>
    if cur.isEmpty then (lines, w)
    else if cur.length + 1 + w.length ≤ width then (lines, cur ++ " " ++ w)
    else (lines ++ [cur], w)
  if cur.isEmpty then lines else lines ++ [cur]

/-- Print text, wrapped to 76 characters. -/
def say (text : String) : IO Unit := do
  for l in wrap 76 text do IO.println l

/-- Print one checker error, wrapped and indented. -/
def sayError (e : String) : IO Unit := do
  for l in wrap 70 s!"ERROR: {e}" do IO.println s!"    {l}"

/-- Print each cheating Adventure with its errors, then the Legal one. -/
def main : IO Unit := do
  say "A cheating DM wrote these Adventures. The checker rejects each one, and a proof in Rpg/Adventures/Lighthouse/NegativeExamples.lean shows the spec rejects it too."
  for a in Tests.cheats do
    IO.println s!"\n* {a.title}"
    for e in check rules mara a do
      sayError e
  IO.println s!"\n* {lighthouse.title}"
  if (check rules mara lighthouse).isEmpty then
    IO.println "    No errors. The theorem `lighthouse_legal` proves it is legal."
  else
    for e in check rules mara lighthouse do
      sayError e
