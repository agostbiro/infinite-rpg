import Rpg.Engine
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
def status (s : FightState) : String :=
  let show1 (f : Fighter) := s!"{f.being.name} {max f.hp 0}/{f.being.maxHP}"
  " | ".intercalate (show1 s.hero :: s.foes.map show1)

/-- The maneuvers the Player can choose in a Fight, in menu order. -/
def maneuverMenu : List Maneuver := [.attack, .allOutAttack, .allOutDefense]

/-- Ask the Player for a maneuver. Returns `none` at end of input. -/
def askManeuver : IO (Option Maneuver) := do
  IO.println "Your turn. Choose a maneuver:"
  for (m, i) in maneuverMenu.zipIdx do
    IO.println s!"  {i + 1}. {m.describe}"
  let some k ← askChoice maneuverMenu.length | return none
  return some (maneuverMenu.getD k .attack)

/-- Ask the Player which living Creature to attack. Returns its number, or `none` at end of input.
If only one Creature is alive, there is no question. -/
def askTarget (s : FightState) : IO (Option Nat) := do
  let living := s.foes.zipIdx.filter (·.1.alive)
  if living.length = 1 then return living[0]?.map (·.2)
  IO.println "Attack whom?"
  for ((f, _), k) in living.zipIdx do
    IO.println s!"  {k + 1}. {f.being.name}"
  let some k ← askChoice living.length | return none
  return living[k]?.map (·.2)

/-- Run a Fight. Returns the Character's HP after a win, or `none` if the Character dies or input ends.
The Player chooses a maneuver on the Character's turn, after the Creatures that act first. -/
partial def runFight (g : IO.Ref Rng) (hero : Fighter) (foes : List Being) : IO (Option Int) := do
  let order := turnOrder hero.being foes
  let rec loop (s : FightState) (round : Nat) : IO (Option Int) := do
    if !s.hero.alive then
      say s!"{s.hero.being.name} falls. The Adventure is over."
      return none
    if s.foes.all (!·.alive) then
      say "You win the Fight."
      return some s.hero.hp
    IO.println s!"\n-- Round {round}: {status s}"
    let mut st := s
    for who in order do
      if st.over then break
      let (st', log) ← match who with
        | some i => withDice g (foeTurn st i)
        | none =>
          let some m ← askManeuver | return none
          let some t ← if m.attacks then askTarget st else pure (some 0) | return none
          withDice g (heroTurn st m t)
      for l in log do IO.println l
      st := st'
    loop st (round + 1)
  loop { hero := hero, foes := foes.map fun b => { being := b, hp := b.maxHP } } 1

/-- Play an Adventure from a Scene, with the Character at the given HP. -/
partial def play (g : IO.Ref Rng) (hero : Being) (a : Adventure) (hp : Int) (id : SceneId) : IO Unit := do
  let some scene := a.scene? id
    | say s!"(Scene {id} is missing. This cannot happen in a Legal Adventure.)"
  IO.println s!"\n== {scene.title} ==   [{hero.name} HP {hp}/{hero.maxHP}]"
  say scene.text
  if scene.choices.isEmpty then
    IO.println "\n*** THE END ***"
    return
  for (ch, i) in scene.choices.zipIdx do
    IO.println s!"  {i + 1}. {ch.text}"
  let some k ← askChoice scene.choices.length | return
  let some ch := scene.choices[k]? | return
  match ch.outcome with
  | .goto n => play g hero a hp n
  | .roll t m onS onF =>
    let level := (hero.rollLevel t).map (· + m)
    let label := if m = 0 then t.name else if m > 0 then s!"{t.name} +{m}" else s!"{t.name} {m}"
    let (res, line) ← withDice g (makeRoll label level)
    IO.println line
    play g hero a hp (if res.succeeded then onS else onF)
  | .fight foes onWin =>
    match ← runFight g { being := hero, hp := hp } foes with
    | some hp' => play g hero a hp' onWin
    | none => return

/-- Show the checker catching each cheating Adventure. -/
def showCheats : IO Unit := do
  say "\nA cheating DM wrote these Adventures. The checker rejects each one, and a proof in Rpg/Adventures/Illegal.lean shows the spec rejects it too."
  for a in cheats do
    IO.println s!"\n* {a.title}"
    for e in check mara a do
      say s!"  ERROR: {e}"
  IO.println s!"\n* {lighthouse.title}"
  let errs := check mara lighthouse
  if errs.isEmpty then
    say "  No errors. The theorem `lighthouse_legal` proves it is legal."

/-- Read `--seed N` from the command line. -/
def seedArg : List String → Option Nat
  | "--seed" :: n :: _ => n.toNat?
  | _ :: rest => seedArg rest
  | [] => none

def main (args : List String) : IO Unit := do
  let seed ← match seedArg args with
    | some s => pure s
    | none => IO.monoNanosNow
  let g ← IO.mkRef (Rng.mk seed.toUInt64)
  IO.println "VERIFIED RPG: a GURPS Lite adventure where the DM cannot cheat."
  IO.println s!"(dice seed {seed}; replay with --seed {seed})"
  IO.println "\n  1. Play The Drowned Lighthouse, as Mara the sellsword"
  IO.println "  2. Watch the checker catch a cheating DM"
  match ← askChoice 2 with
  | some 0 =>
    -- Check the Adventure again, on the value the program will play.
    -- The theorem covers the value Lean proved things about. A trick such as `implemented_by`
    -- can make the compiled value different, and this check catches that.
    let errs := checkCharacter mara ++ check mara lighthouse
    if !errs.isEmpty then
      say "\nThe Adventure failed the check, so the game will not start:"
      for e in errs do say s!"  ERROR: {e}"
      return
    say s!"\nMara: ST {mara.st}, DX {mara.dx}, IQ {mara.iq}, HT {mara.ht}, HP {mara.maxHP}, Dodge {mara.dodge}. Broadsword-14, leather armor (DR 2)."
    play g mara lighthouse mara.maxHP lighthouse.start
  | some _ => showCheats
  | none => pure ()
