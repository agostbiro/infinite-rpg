import Rpg.Engine
import Rpg.Catalog
import Rpg.Adventures.Illegal

/-!
# Terminal game

This file reads the Player's input and prints text. All game rules are in the `Rpg` modules.
-/

open Rpg

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

/-- Ask the Player for a number from 1 to `n`. Returns `none` at end of input. -/
partial def askChoice (n : Nat) : IO (Option Nat) := do
  IO.print "> "
  (← IO.getStdout).flush
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then return none
  match (String.ofList (line.toList.filter Char.isDigit)).toNat? with
  | some k => if 1 ≤ k ∧ k ≤ n then return some (k - 1) else askChoice n
  | none => askChoice n

/-- Run an Engine step that uses dice. -/
def withDice (g : IO.Ref Rng) (x : Roll α) : IO α := do
  let (a, s) := x.run (← g.get)
  g.set s
  return a

/-- One line that shows the HP of every being in a Fight. -/
def status (rules : RuleSet) (s : FightState) : String :=
  let show1 (f : Fighter) := s!"{f.being.name} {max f.hp 0}/{rules.maxHP f.being}"
  " | ".intercalate (show1 s.hero :: s.foes.map show1)

/-- Run a Fight. Returns the Character's HP after a win, or `none` if the Character dies or input ends. -/
partial def runFight (rules : RuleSet) (g : IO.Ref Rng) (hero : Fighter) (foes : List Being) : IO (Option Int) := do
  let order := turnOrder rules hero.being foes
  let rec loop (s : FightState) (round : Nat) : IO (Option Int) := do
    if !s.hero.alive then
      say s!"{s.hero.being.name} falls. The Adventure is over."
      return none
    if s.foes.all (!·.alive) then
      say "You win the Fight."
      return some s.hero.hp
    IO.println s!"\n-- Round {round}: {status rules s}"
    let living := (s.foes.zipIdx.filter fun (f, _) => f.alive).map (·.2)
    let target ← if living.length = 1 then pure (living.getD 0 0) else do
      IO.println "Attack whom?"
      for (i, k) in living.zipIdx do
        IO.println s!"  {k + 1}. {(s.foes.getD i hero).being.name}"
      match ← askChoice living.length with
      | some k => pure (living.getD k 0)
      | none => return none
    let (s', log) ← withDice g (fightRound rules order s target)
    for l in log do IO.println l
    loop s' (round + 1)
  loop ⟨hero, foes.map fun b => ⟨b, rules.maxHP b⟩⟩ 1

/-- Play an Adventure from a Scene, with the Character at the given HP. -/
private partial def play (rules : RuleSet) (g : IO.Ref Rng) (hero : Being) (a : Adventure) (hp : Int) (id : SceneId) : IO Unit := do
  let some scene := a.scene? id
    | say s!"(Scene {id} is missing. This cannot happen in a Legal Adventure.)"
  IO.println s!"\n== {scene.title} ==   [{hero.name} HP {hp}/{rules.maxHP hero}]"
  say scene.text
  if scene.choices.isEmpty then
    IO.println "\n*** THE END ***"
    return
  for (ch, i) in scene.choices.zipIdx do
    IO.println s!"  {i + 1}. {ch.text}"
  let some k ← askChoice scene.choices.length | return
  let some ch := scene.choices[k]? | return
  match ch.outcome with
  | .goto n => play rules g hero a hp n
  | .roll t m onS onF =>
    let level := (hero.rollLevel rules t).map (· + m)
    let label := if m = 0 then t.name else if m > 0 then s!"{t.name} +{m}" else s!"{t.name} {m}"
    let (res, line) ← withDice g (makeRoll rules label level)
    IO.println line
    play rules g hero a hp (if res.succeeded then onS else onF)
  | .fight foes onWin =>
    match ← runFight rules g ⟨hero, hp⟩ foes with
    | some hp' => play rules g hero a hp' onWin
    | none => return

/-- Start a story admitted by the source-bound statistical confidence protocol. -/
def playStatistical (g : IO.Ref Rng) (a : Probability.StatisticalAdventure) : IO Unit := do
  let candidate := a.candidate
  say s!"\n{candidate.hero.name}: HP {candidate.rules.maxHP candidate.hero}, Dodge {candidate.rules.dodge candidate.hero}."
  play candidate.rules g candidate.hero candidate.story (candidate.rules.maxHP candidate.hero) candidate.story.start

/-- Show the checker catching each cheating Adventure. -/
def showCheats : IO Unit := do
  say "\nA cheating DM wrote these Adventures. The checker rejects each one, and a proof in Rpg/Adventures/Illegal.lean shows the spec rejects it too."
  for a in Lighthouse.Tests.cheats do
    IO.println s!"\n* {a.title}"
    for e in check Lighthouse.rules Lighthouse.mara a do
      say s!"  ERROR: {e}"
  IO.println s!"\n* {Lighthouse.lighthouse.title}"
  let errs := check Lighthouse.rules Lighthouse.mara Lighthouse.lighthouse
  if errs.isEmpty then
    say "  Legality passes. Lighthouse must also pass the statistical confidence protocol before play."

/-- Read `--seed N` from the command line. -/
def seedArg : List String → Option Nat
  | "--seed" :: n :: _ => n.toNat?
  | _ :: rest => seedArg rest
  | [] => none

def main (args : List String) : IO Unit := do
  if args.contains "--cheats" then
    showCheats
    return
  let seed ← match seedArg args with
    | some s => pure s
    | none => IO.monoNanosNow
  let g ← IO.mkRef (Rng.mk seed.toUInt64)
  IO.println "VERIFIED RPG: adventures checked for legality and fairness."
  IO.println s!"(dice seed {seed}; replay with --seed {seed})"
  let mut choices : List Probability.StatisticalAdventure := []
  for candidate in statisticalCandidates do
    IO.println s!"Checking {candidate.story.title} with the fixed confidence protocol..."
    (← IO.getStdout).flush
    let (counts, admitted) := Probability.admitStatistically candidate
    match admitted with
    | some evidence =>
      say s!"{candidate.story.title}: passed the finite fairness confidence check ({counts.games} validation games)."
      choices := choices ++ [evidence]
    | none =>
      say s!"{candidate.story.title}: not admitted; validation failed or was incomplete. Run make validate for details."
  for (entry, i) in choices.zipIdx do
    IO.println s!"  {i + 1}. Play {entry.candidate.story.title}, as {entry.candidate.hero.name} [fairness checked through death turn {entry.candidate.horizon + 1}]"
  let demo := choices.length + 1
  IO.println s!"  {demo}. Watch the checker catch a cheating DM"
  match ← askChoice demo with
  | some k =>
    match choices[k]? with
    | some a => playStatistical g a
    | none => showCheats
  | none => pure ()
