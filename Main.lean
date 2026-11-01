import Rpg.Prompt
import Rpg.Catalog
import Std.Http

/-!
# Game server

This program serves the game to a browser with core `Std.Http`. By default it listens on
`localhost` (127.0.0.1) only. `--host A.B.C.D` makes it listen on that IPv4 (Internet Protocol
version 4) address instead, for example to play from the host of a VM (virtual machine).
It keeps one game in memory. The page draws the view that the server sends,
and sends back the Player's inputs. All rules and dice stay in Lean (`Rpg.step`).

The Player can also type a Wish. The server then asks the Claude API for an Adventure and a
Character, in the background, and checks them with the proved checker and then the fairness check
(`Draft.toGame`).
Only a Draft that passes can become a `Game`, because `Game.new` needs the proofs.
Adventures that pass are saved under `adventures/<id>/`.

Routes:

* `GET /api/view`: the current view, with the state of the Wish and the saved Adventures.
* `POST /api/input`: apply one input (JSON). A refused input gives status 400, an error, and the
  view, and changes nothing.
* `POST /api/new`: start the same Adventure again, on the title screen, with a new seed.
* `POST /api/builtin`: go back to The Drowned Lighthouse.
* `POST /api/wish`: ask the DM for an Adventure. The body is `{"wish", "name", "gender"}`.
* `POST /api/retry`: ask again with the last Wish, after 3 failed tries.
* `POST /api/dismiss`: hide the result of a failed or refused Wish.
* `POST /api/cancel`: stop the DM.
* `POST /api/load`: play a saved Adventure. The body is `{"id"}`. It is checked again first.
* `GET /saved/<id>/<name>.svg`: a Picture of the saved Adventure in play, if it passed the check.
* `GET /<file>`: a file from `web/`. `/` is `web/index.html`.

While the DM writes, every POST other than `/api/cancel` gets 409.
Every POST must have `Content-Type: application/json`, and its `Origin`, if any, must be this
server. Else the reply is 403. This stops other websites in the Player's browser from driving
the game. A body over 4 KB gets 413.

This code has no proofs. The proofs are about `Rpg.step` and `Rpg.check`, which this code calls.
-/

open Std Async Http Server
open Lean (Json toJson fromJson?)
open Rpg

/-! ## Sessions -/

/-- The one game the server keeps, with its dice and every Report since it began. -/
structure Session where
  /-- The game on its title screen, for "Play again". -/
  fresh : Game
  game : Game
  dice : Rng
  seed : Nat
  reports : Array Report

/-- A new session of a game, from its title screen. -/
def Session.start (g : Game) (seed : Nat) : Session :=
  { fresh := g, game := g, dice := ⟨seed.toUInt64⟩, seed, reports := #[] }

/-- The built-in game: The Drowned Lighthouse for Mara. The proofs are the shipped theorems.
`main` runs the fairness check on it before the server starts, and stops if it fails. -/
def builtinGame : Game := Game.new Lighthouse.lighthouseDefinition

/-- Apply one input. Returns the new session, or the reason the input was refused.
A refused input leaves the session as it was. -/
def Session.apply (s : Session) (i : Input) : Session × Option String × Nat :=
  let ((g, reports), dice) := (step s.game i).run s.dice
  match reports.find? (·.isRejected) with
  | some (.rejected why) => (s, some why, 0)
  | _ => ({ s with game := g, dice, reports := s.reports ++ reports.toArray }, none, reports.length)

/-! ## Server state -/

/-- Where the Adventure in play comes from, and its Pictures. -/
structure Source where
  /-- The folder name under `adventures/`, or `none` for the built-in Adventure. -/
  savedId : Option String := none
  /-- The Character's background, for a live Adventure. -/
  background : Option String := none
  /-- The Pictures that passed the check and can be served. -/
  pictures : List String := []
  /-- The Pictures the DM is drawing now. A Picture in neither list shows the plain backdrop. -/
  drawing : List String := []
  /-- The number of the current drawing run. A run that is not current stops. -/
  drawRun : Nat := 0

/-- What the DM is doing with a Wish. -/
inductive GenState where
  | idle
  | running
  | failed
  | refused
  deriving BEq

/-- The name of a state, for the page. -/
def GenState.name : GenState → String
  | .idle => "idle"
  | .running => "running"
  | .failed => "failed"
  | .refused => "refused"

/-- One step of the work on a Wish, shown on the page. -/
structure Step where
  text : String
  errors : List String := []
  deriving Lean.ToJson

/-- The work on the last Wish. -/
structure Generation where
  /-- The number of the current or last job. Cancel moves it on, so an old job can tell. -/
  job : Nat := 0
  state : GenState := .idle
  steps : Array Step := #[]
  /-- The last Wish, name, and gender, for "Try again". -/
  wish : String := ""
  name : String := ""
  gender : String := ""

/-- Everything the server keeps. -/
structure ServerState where
  session : Session
  /-- The number of the last drawing run, so each run gets a new number. -/
  runs : Nat := 0
  source : Source := {}
  gen : Generation := {}

/-- A checked entry of the saved list: the folder, a stamp of its content (length and hash), the title,
and `none` if the Adventure passes the checker, or else the first error. -/
abbrev SavedEntry := String × String × String × Option String

/-- Settings that do not change while the server runs. -/
structure GameConfig where
  host : String
  port : Nat
  /-- The Claude API key, from `ANTHROPIC_API_KEY`. -/
  apiKey : Option String
  /-- Test hook: a folder of recorded API replies to use instead of calling the API
  (`RPG_FAKE_API`). -/
  fake : Option System.FilePath
  /-- The saved list, checked once per version of each file, so the title screen stays fast. -/
  savedCache : IO.Ref (List SavedEntry)
  /-- `true` if the Picture check (`scripts/check_pictures.py`) could run when the server started.
  If it is `false`, Pictures are off: the server never asks the DM for a Picture, because it could
  never serve one. -/
  picturesOn : Bool

/-- `true` if the server can ask the DM for an Adventure. -/
def GameConfig.canWish (c : GameConfig) : Bool := c.apiKey.isSome || c.fake.isSome

/-- The running `curl` processes. Each has an owner, such as "job-3" for a Wish or
"pictures-2-the-shire" for the Pictures of a saved Adventure, so the server can stop them. -/
abbrev Children := IO.Ref (Array (String × Nat × IO Unit))

/-- The owner name of the `curl` processes of Wish job `job`. -/
def jobOwner (job : Nat) : String := s!"job-{job}"

/-- The owner name of the `curl` processes that draw the Pictures of saved Adventure `id`. -/
def picturesOwner (id : String) : String := s!"pictures-{id}"

/-- Kill every `curl` process of an owner. -/
def killOwner (children : Children) (owner : String) : IO Unit := do
  for (o, _, kill) in ← children.get do
    if o == owner then try kill catch _ => pure ()

/-! ## The folder of saved Adventures -/

/-- The folder of saved Adventures. -/
def savedRoot : System.FilePath := "adventures"

/-- A path segment is safe if it has only letters, digits, `-`, `_`, and `.`, and does not start
with `.`. So `..`, hidden files, and encoded characters such as `%2e` are refused. -/
def safeSegment (seg : String) : Bool :=
  !seg.isEmpty && !seg.startsWith "." &&
    seg.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- A short folder name from a title, such as "the-shire-errand". -/
def slug (title : String) : String :=
  let raw := title.toList.map fun c => if c.isAlphanum && c.toNat < 128 then c.toLower else '-'
  let parts := (String.ofList raw).splitOn "-" |>.filter (!·.isEmpty)
  let s := ("-".intercalate parts).take 30 |>.toString
  if s.isEmpty then "adventure" else s

#guard slug "The Shire: An Errand!" == "the-shire-an-errand"
#guard slug "???" == "adventure"

/-- The number at the front of a folder name such as "3-the-shire", or 0. -/
def idNumber (id : String) : Nat := ((id.splitOn "-").headD "").toNat?.getD 0

/-- The folders of saved Adventures. -/
def savedIds : IO (List String) := do
  if !(← savedRoot.isDir) then return []
  let entries ← savedRoot.readDir
  let ids := entries.toList.map (·.fileName) |>.filter safeSegment
  let mut out := []
  for id in ids do
    if ← (savedRoot / id / "adventure.json").pathExists then out := out ++ [id]
  return out.mergeSort fun a b => idNumber a ≥ idNumber b

/-- A new folder name for a saved Adventure. -/
def newSavedId (title : String) : IO String := do
  let ids ← savedIds
  let n := (ids.map idNumber).foldl max 0 + 1
  return s!"{n}-{slug title}"

/-- Read a file, or give the error. -/
def readText (p : System.FilePath) : IO (Except String String) := do
  try return .ok (← IO.FS.readFile p) catch e => return .error (toString e)

/-- A stamp of a file that changes when its content changes: its length and a hash of its content.
The time of the file is not used, because it can be set back (`touch -r`). -/
def fileStamp (p : System.FilePath) : IO String := do
  match ← readText p with
  | .ok text => return s!"{text.length}/{hash text}"
  | .error _ => return ""

/-- The fairness seed saved with an Adventure, or `none` if it has none (it was saved before
the fairness check). -/
def savedSeed (text : String) : Option Nat :=
  (Json.parse text >>= (·.getObjValAs? Nat "fairnessSeed")).toOption

/-- Check a saved Adventure again: the checker, then the fairness check with its saved seed. -/
def checkSavedText (text : String) : Except (List String) (Draft × Game) := do
  let d ← (Draft.parse text).mapError (fun e => [e])
  let some seed := savedSeed text
    | throw ["it was saved before the fairness check, so it has no fairness seed"]
  let g ← d.toGame seed
  return (d, g)

/-- Check one saved Adventure for the list: its title, and `none` if it passes the checker and
the fairness check, or else the first error. The Pictures are checked only on load. -/
def checkSavedEntry (id : String) : IO (String × Option String) := do
  match ← readText (savedRoot / id / "adventure.json") with
  | .error e => return (id, some e)
  | .ok text =>
    let title := (Json.parse text >>= (·.getObjValAs? String "title")).toOption.getD id
    match checkSavedText text with
    | .ok _ => return (title, none)
    | .error errs => return (title, some (errs.headD "it fails the checker"))

/-- The list of saved Adventures for the title screen: each id, title, and whether it passes the
checker now. A saved Adventure that fails is listed with `ok: false` and the reason, and the page
does not let the Player play it. Each file is checked once per version (see `GameConfig.savedCache`). 
Each check also runs the fairness check (1,000 games), so the first view after start can take
a second or two for each saved Adventure. -/
def savedList (cfg : GameConfig) : IO Json := do
  let cache ← cfg.savedCache.get
  let mut fresh : List SavedEntry := []
  let mut out := #[]
  for id in ← savedIds do
    let stamp ← fileStamp (savedRoot / id / "adventure.json")
    let (title, why) ← match cache.find? fun (i, st, _, _) => i == id && st == stamp with
      | some (_, _, t, w) => pure (t, w)
      | none => checkSavedEntry id
    fresh := fresh ++ [(id, stamp, title, why)]
    out := out.push (json% { id: $(id), title: $(title), ok: $(why.isNone), why: $(why) })
  cfg.savedCache.set fresh
  return Json.arr out

/-- Record in the cache that saved Adventure `id`, as its file is now, was refused on load. -/
def markRefused (cfg : GameConfig) (id : String) (why : String) : IO Unit := do
  let stamp ← fileStamp (savedRoot / id / "adventure.json")
  cfg.savedCache.modify fun c =>
    c.map fun (i, st, t, w) => if i == id then (i, stamp, t, some why) else (i, st, t, w)

/-- Save a Draft that passed the checker and the fairness check with seed `seed`. -/
def saveDraft (id : String) (d : Draft) (wish : String) (seed : Nat) : IO Unit := do
  let dir := savedRoot / id
  IO.FS.createDirAll dir
  let j := (d.toJson.setObjVal! "wish" (Json.str wish)).setObjVal! "fairnessSeed" (toJson seed)
  IO.FS.writeFile (dir / "adventure.json") j.pretty

/-! ## Pictures -/

/-- The most characters in one Picture. -/
def maxPicture : Nat := 100000

/-- The result of the Picture check on one file. -/
inductive PictureCheck where
  /-- The check ran and found no problem. The Picture can be served. -/
  | ok
  /-- The check ran and rejected the Picture (exit code 1). -/
  | refused
  /-- The check could not run: no `python3`, no script, or an error in it (any other exit code).
  The Picture is not served, and it is not recorded as refused, so it can be drawn again. -/
  | cannotCheck
  deriving BEq

/-- Run `scripts/check_pictures.py` on folders or files. -/
def runPictureCheck (paths : Array String) : IO PictureCheck := do
  try
    let out ← IO.Process.output { cmd := "python3", args := #["scripts/check_pictures.py"] ++ paths }
    match out.exitCode with
    | 0 => return .ok
    | 1 =>
      IO.eprintln s!"Picture refused: {out.stdout.trimAscii}"
      return .refused
    | c =>
      IO.eprintln s!"The Picture check could not run (exit code {c}): {out.stdout.trimAscii} {out.stderr.trimAscii}"
      return .cannotCheck
  catch e =>
    IO.eprintln s!"The Picture check could not run: {e}"
    return .cannotCheck

/-- Run the Picture check on one file. -/
def checkPicture (path : System.FilePath) : IO PictureCheck := runPictureCheck #[path.toString]

/-- The file that lists the Pictures of a saved Adventure that the DM drew and the check refused,
one name per line. They are not drawn again, so a bad Picture costs one API call, not one per load. -/
def refusedFile (id : String) : System.FilePath := savedRoot / id / "refused-pictures.txt"

/-- The Pictures of saved Adventure `id` that the check refused. -/
def refusedPictures (id : String) : IO (List String) := do
  match ← readText (refusedFile id) with
  | .ok t => return (t.splitOn "\n").filter (!·.isEmpty)
  | .error _ => return []

/-- Record that the check refused Picture `name` of saved Adventure `id`. -/
def recordRefused (id name : String) : IO Unit := do
  try
    let h ← IO.FS.Handle.mk (refusedFile id) .append
    h.putStrLn name
  catch _ => pure ()

/-- The Scenes of a saved Adventure whose Pictures must still be drawn: no file on disk, and not
refused before. -/
def missingPictures (id : String) (a : Adventure) : IO (List Scene) := do
  let refused ← refusedPictures id
  a.scenes.filterM fun sc => do
    let some name := sc.picture | return false
    if !safePicture name || refused.contains name then return false
    return !(← (savedRoot / id / s!"{name}.svg").pathExists)

/-- The Pictures of a saved Adventure that pass the check now. -/
def checkedPictures (id : String) (a : Adventure) : IO (List String) := do
  let mut ok := []
  for sc in a.scenes do
    let some name := sc.picture | continue
    let path := savedRoot / id / s!"{name}.svg"
    if !safePicture name then continue
    if !(← path.pathExists) then continue
    if (← checkPicture path) == .ok then ok := ok ++ [name]
  return ok

/-! ## Calling the Claude API -/

/-- The headers for the API, one per line. `curl` reads them from its standard input, so the
key is never on a command line. -/
def apiHeaders (key : String) : String :=
  "content-type: application/json\n" ++
  s!"x-api-key: {key}\n" ++
  "anthropic-version: 2026-10-21\n" ++
  "anthropic-beta: server-side-fallback-2026-07-01\n"

/-- Run `curl` once. Returns the HTTP status and the body. The process is listed under `owner`, so
the server can kill it. If `wanted` is already false once it is listed, it is killed at once. -/
def curlOnce (children : Children) (owner : String) (wanted : IO Bool) (key : String)
    (body : String) : IO (Nat × String) := do
  let (h, bodyPath) ← IO.FS.createTempFile
  h.putStr body
  h.flush
  try
    let child ← IO.Process.spawn {
      cmd := "curl",
      -- The reply streams, so it is rarely idle for long. Stop if it sends less than 1 byte a
      -- second for 10 minutes (a long, quiet think can be slow), and stop after 30 minutes in all.
      args := #["-sS", "--max-time", "1800", "--speed-limit", "1", "--speed-time", "600", "-X", "POST",
        "https://api.anthropic.com/v1/messages",
        "-H", "@-", "--data-binary", s!"@{bodyPath}", "-w", "\n%{http_code}"],
      stdin := .piped, stdout := .piped, stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr (apiHeaders key)
    stdin.flush
    let uid ← IO.monoNanosNow
    children.modify (·.push (owner, uid, child.kill))
    -- A Cancel between the check in `callApi` and the line above did not see this process.
    if !(← wanted) then try child.kill catch _ => pure ()
    let out ← IO.asTask child.stdout.readToEnd .dedicated
    let err ← child.stderr.readToEnd
    let code ← child.wait
    children.modify (·.filter (·.2.1 != uid))
    let out ← IO.ofExcept out.get
    if code != 0 then
      return (0, s!"curl failed ({code}): {err.trimAscii}")
    let lines := out.splitOn "\n"
    let status := (lines.getLast?.getD "").trimAscii.toString.toNat?.getD 0
    return (status, "\n".intercalate lines.dropLast)
  finally
    try IO.FS.removeFile bodyPath catch _ => pure ()

/-- The reply when the work was stopped, for example by Cancel. -/
def stoppedReply : Reply := .failed "stopped"

/-- Send one request to the API, or read a recorded reply in test mode. `fixtures` names the
recorded replies to try, such as "adventure-2". Busy or failing servers get two more tries.
`wanted` says if the work is still wanted. It is checked before each try and after each try,
so a request that Cancel stopped is never sent again. -/
def callApi (cfg : GameConfig) (children : Children) (owner : String) (wanted : IO Bool) (req : Json)
    (fixtures : List String) : IO Reply := do
  if !(← wanted) then return stoppedReply
  if let some dir := cfg.fake then
    -- Test hook: wait a little, so the page can show the steps, then read a recorded reply.
    IO.sleep 1500
    if !(← wanted) then return stoppedReply
    for f in fixtures do
      let p := dir / s!"{f}.sse"
      if ← p.pathExists then return (parseStreamReply (← IO.FS.readFile p)).2
    return .failed s!"test mode: no recorded reply {fixtures.headD ""}.sse in {dir}"
  let some key := cfg.apiKey | return .failed "ANTHROPIC_API_KEY is not set"
  let body := req.compress
  let mut last := Reply.failed "no reply"
  for wait in [0, 5000, 20000] do
    if wait > 0 then IO.sleep wait.toUInt32
    if !(← wanted) then return stoppedReply
    let (status, text) ← curlOnce children owner wanted key body
    -- A killed `curl` also gives status 0. Never try again for work that was stopped.
    if !(← wanted) then return stoppedReply
    -- A reply of 200 is a stream of events. Any other status has a plain JSON error body.
    let (status, reply) :=
      if status == 200 then parseStreamReply text
      else if status == 0 then (0, Reply.failed text)
      else (status, parseReply text)
    last := reply
    if ![0, 429, 500, 502, 503, 504, 529].contains status then return last
  return last

/-! ## Working on a Wish, in the background -/

/-- Change the work on job `job`, if it is still the current job. Returns `false` if it is not
(for example, after Cancel). -/
def updateJob (ref : IO.Ref ServerState) (job : Nat) (f : Generation → Generation) : IO Bool :=
  ref.modifyGet fun s =>
    if s.gen.job == job && s.gen.state == .running then (true, { s with gen := f s.gen })
    else (false, s)

/-- `true` while job `job` is the current Wish and still runs. -/
def jobWanted (ref : IO.Ref ServerState) (job : Nat) : IO Bool := do
  let s ← ref.get
  return s.gen.job == job && s.gen.state == .running

/-- `true` while the saved Adventure `id` is the one in play and drawing run `run` is current,
so its Pictures are wanted. -/
def picturesWanted (ref : IO.Ref ServerState) (id : String) (run : Nat) : IO Bool := do
  let s ← ref.get
  return s.source.savedId == some id && s.source.drawRun == run

/-- End job `job` in the state `st`, with a last step. -/
def endJob (ref : IO.Ref ServerState) (job : Nat) (st : GenState) (last : Step) : IO Unit := do
  let _ ← updateJob ref job fun g => { g with state := st, steps := g.steps.push last }

/-- Add a step to job `job`. -/
def addStep (ref : IO.Ref ServerState) (job : Nat) (st : Step) : IO Bool :=
  updateJob ref job fun g => { g with steps := g.steps.push st }

/-- The folder where drawing run `run` writes a Picture before the check. Each run has its own
folder, so one run never deletes another run's file. The name is "drawing-" and digits only. -/
def draftFolder (id : String) (run : Nat) : System.FilePath := savedRoot / id / s!"drawing-{run}"

/-- `true` for the name of a draft folder: "drawing" (an older form) or "drawing-" and digits. -/
def isDraftFolder (name : String) : Bool :=
  name == "drawing" ||
    (name.startsWith "drawing-" && (name.drop 8).toString.length > 0 && (name.drop 8).toString.all Char.isDigit)

#guard isDraftFolder "drawing-12" && isDraftFolder "drawing" && !isDraftFolder "drawing-" &&
  !isDraftFolder "drawing-1/.." && !isDraftFolder "scene-1.svg"

/-- Remove the draft folders of saved Adventure `id` that are left from older runs. -/
def cleanDraftFolders (id : String) : IO Unit := do
  let entries ← try (savedRoot / id).readDir catch _ => pure #[]
  for e in entries do
    if !isDraftFolder e.fileName then continue
    if !(← e.path.isDir) then continue
    try IO.FS.removeDirAll e.path catch _ => pure ()

/-- Draw the Picture of one Scene, check it, and keep it if it passes. -/
def drawPicture (cfg : GameConfig) (children : Children) (ref : IO.Ref ServerState) (id : String)
    (run : Nat) (d : Draft) (sc : Scene) : IO Unit := do
  let some name := sc.picture | return
  -- Skip the work if another Adventure, or another drawing run, is current now.
  if !(← picturesWanted ref id run) then return
  let ok ← try
    let reply ← callApi cfg children (picturesOwner id) (picturesWanted ref id run)
      (pictureRequest d.adventure d.palette sc) [s!"picture-{sc.id}", "picture"]
    -- Write nothing for a run that is no longer current.
    if !(← picturesWanted ref id run) then return
    match reply with
    | .ok text _ =>
      match Json.parse text >>= (·.getObjValAs? String "svg") with
      | .ok svg =>
        if !safePicture name then pure false else
        if svg.length > maxPicture then
          recordRefused id name
          pure false
        else
        let draft := draftFolder id run
        IO.FS.createDirAll draft
        let tmp := draft / s!"{name}.svg"
        IO.FS.writeFile tmp svg
        match ← checkPicture tmp with
        | .ok =>
          IO.FS.rename tmp (savedRoot / id / s!"{name}.svg")
          pure true
        | .refused =>
          IO.FS.removeFile tmp
          recordRefused id name
          pure false
        | .cannotCheck =>
          -- Not served and not recorded: a later load draws it again.
          IO.FS.removeFile tmp
          pure false
      | .error _ => pure false
    | _ => pure false
    catch e =>
      IO.eprintln s!"Picture {name} failed: {e}"
      pure false
  ref.modify fun s =>
    if s.source.savedId != some id || s.source.drawRun != run then s else
    let src := s.source
    -- A Picture is listed once.
    { s with source := { src with
        drawing := src.drawing.erase name,
        pictures := if ok && !src.pictures.contains name then src.pictures ++ [name] else src.pictures } }

/-- Draw the Pictures of these Scenes in drawing run `run`, at most 4 at a time. -/
def drawPictures (cfg : GameConfig) (children : Children) (ref : IO.Ref ServerState) (id : String)
    (run : Nat) (d : Draft) (scenes : List Scene) : IO Unit := do
  let rec chunks : Nat → List Scene → List (List Scene)
    | 0, _ => []
    | n + 1, xs => if xs.isEmpty then [] else xs.take 4 :: chunks n (xs.drop 4)
  for group in chunks scenes.length scenes do
    let tasks ← group.mapM fun sc => IO.asTask (drawPicture cfg children ref id run d sc) .dedicated
    for t in tasks do
      let _ ← IO.wait t
  -- Remove this run's folder of unchecked drafts. Other runs have their own folders.
  try IO.FS.removeDirAll (draftFolder id run) catch _ => pure ()

/-- Start play of a Draft that passed: save it, make it the session, and draw its Pictures. -/
def adopt (cfg : GameConfig) (children : Children) (ref : IO.Ref ServerState) (job : Nat)
    (d : Draft) (g : Game) (wish : String) (fairnessSeed : Nat) : IO Unit := do
  let id ← newSavedId d.adventure.title
  saveDraft id d wish fairnessSeed
  let seed := (← IO.monoNanosNow) % 1000000
  let res ← ref.modifyGet fun s =>
    if s.gen.job != job || s.gen.state != .running then (none, s) else
    let run := s.runs + 1
    (some (s.source.savedId, run), { s with
      session := Session.start g seed,
      runs := run,
      source := { savedId := some id, background := some d.background,
                  drawing := if cfg.picturesOn then d.adventure.scenes.filterMap (·.picture) else [],
                  drawRun := run },
      gen := { s.gen with state := .idle, steps := #[] } })
  if let some (old, run) := res then
    if let some oldId := old then killOwner children (picturesOwner oldId)
    -- With Pictures off, no Picture is asked for.
    if cfg.picturesOn then
      let _ ← IO.asTask (drawPictures cfg children ref id run d d.adventure.scenes) .dedicated

/-- The step text for the errors of the checker and the fairness check. -/
def errorsText (n : Nat) : String :=
  if n = 1 then "The checks found 1 error:" else s!"The checks found {n} errors:"

/-- A random seed for the fairness check of a Wish, from the operating system. -/
def randomSeed : IO Nat := do
  let bytes ← IO.getRandomBytes 8
  return bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Ask the DM for an Adventure for a Wish: up to 3 tries. After a failed try, the DM gets the
errors and sends a fixed version. -/
def generate (cfg : GameConfig) (children : Children) (ref : IO.Ref ServerState) (job : Nat)
    (wish name gender : String) : IO Unit := do
  let mut messages := [userTurn (wishMessage wish name gender)]
  let mut lastErrors : List String := []
  for attempt in [1, 2, 3] do
    let text := if attempt == 1 then "The DM is writing..." else "The DM is fixing them..."
    if !(← addStep ref job { text }) then return
    let reply ← callApi cfg children (jobOwner job) (jobWanted ref job) (adventureRequest messages)
      [s!"adventure-{attempt}"]
    if !(← jobWanted ref job) then return
    let (errors, hero?, content) ← match reply with
      | .refused =>
        endJob ref job .refused { text := "The DM won't write that one. Try another Wish." }
        return
      | .failed why =>
        endJob ref job .failed { text := "The DM could not be reached.", errors := [why] }
        return
      | .cutOff content =>
        pure (["the reply was cut off because it was too long. Write fewer or shorter Scenes"],
          none, content)
      | .ok text content =>
        match Draft.parse text with
        | .error e => pure ([s!"the JSON does not read: {e}"], none, content)
        | .ok d =>
          -- A fresh random seed for each try, so the DM cannot tune its story to one batch of games.
          -- In test mode (`RPG_FAKE_API`) the seed is fixed, so `make run-fake` gives the same result each time.
          let fairnessSeed ← if cfg.fake.isSome then pure 1 else randomSeed
          match d.toGame fairnessSeed with
          | .ok g =>
            if !(← addStep ref job { text := "The Adventure passed the checker and the fairness check." }) then return
            adopt cfg children ref job d g wish fairnessSeed
            return
          | .error errs => pure (errs, some d.hero, content)
    lastErrors := errors
    if !(← addStep ref job { text := errorsText errors.length, errors }) then return
    messages := messages ++ [assistantTurn content, userTurn (fixMessage errors hero?)]
  endJob ref job .failed
    { text := "The DM could not write a legal and fair Adventure in 3 tries.", errors := lastErrors }

/-- Start the work on a Wish in the background. Returns `false`, and does nothing, if the DM is
already writing. The check and the start are one atomic step. -/
def startWish (cfg : GameConfig) (children : Children) (ref : IO.Ref ServerState)
    (wish name gender : String) : IO Bool := do
  let job? ← ref.modifyGet fun s =>
    if s.gen.state == .running then (none, s) else
    let job := s.gen.job + 1
    (some job, { s with gen := { job, state := .running, wish, name, gender } })
  let some job := job? | return false
  let _ ← IO.asTask (prio := .dedicated) do
    try generate cfg children ref job wish name gender
    catch e =>
      endJob ref job .failed { text := "Something went wrong.", errors := [toString e] }
  return true

/-- Stop the work on the current Wish, and kill its `curl` processes. -/
def cancelWish (children : Children) (ref : IO.Ref ServerState) : IO Unit := do
  -- First move the job on, so the old job sees that it is not wanted. Then kill its processes.
  let old ← ref.modifyGet fun s =>
    (s.gen.job, { s with gen := { s.gen with job := s.gen.job + 1, state := .idle, steps := #[] } })
  killOwner children (jobOwner old)

/-! ## The view -/

/-- The number of Pictures of the Adventure in play that show the plain backdrop: neither ready
nor drawing now. It is worked out from the state each time, so it never goes stale.
With Pictures off it is 0: no Picture was tried, so none failed. -/
def failedPictures (cfg : GameConfig) (s : ServerState) : Nat :=
  if !cfg.picturesOn then 0 else
  let src := s.source
  (s.session.game.adventure.scenes.filterMap (·.picture)).filter
    (fun n => !src.pictures.contains n && !src.drawing.contains n) |>.length

/-- The whole view: the game, plus the Wish, the Pictures, and the saved Adventures. -/
def fullView (cfg : GameConfig) (s : ServerState) (fresh : Nat := 0) (error : Option String := none) :
    IO String := do
  let g := s.session
  let base := (viewJson g.game g.seed g.reports fresh error)
  let pictures := match s.source.savedId with
    | none => json% { base: "/pictures/", ready: null, drawing: 0, failed: 0, off: false }
    | some id => json% { base: $(s!"/saved/{id}/"), ready: $(s.source.pictures),
                         drawing: $(s.source.drawing.length), failed: $(failedPictures cfg s), off: $(!cfg.picturesOn) }
  let gen := json% {
    available: $(cfg.canWish), state: $(s.gen.state.name), steps: $(s.gen.steps),
    wish: $(s.gen.wish), name: $(s.gen.name), gender: $(s.gen.gender)
  }
  let saved ← if g.game.phase.name == "title" then savedList cfg else pure (Json.arr #[])
  let v := base.setObjVal! "pictures" pictures
    |>.setObjVal! "generation" gen
    |>.setObjVal! "saved" saved
    |>.setObjVal! "live" (toJson s.source.savedId.isSome)
    |>.setObjVal! "background" (toJson s.source.background)
  return v.compress

/-! ## Responses -/

/-- The Content Security Policy (CSP): scripts, styles, and images come only from this server.
No inline script runs, and nothing loads from anywhere else. -/
def csp : String :=
  "default-src 'none'; script-src 'self'; style-src 'self'; img-src 'self'; connect-src 'self'; " ++
  "base-uri 'none'; form-action 'none'; frame-ancestors 'none'"

/-- A response with the safety headers on it. -/
def reply (status : Status) (contentType : String) (body : ByteArray) :
    ContextAsync (Response Body.Any) := do
  let r : Response Body.Full ← Response.withStatus status
    |>.header! "Content-Type" contentType
    |>.header! "Content-Security-Policy" csp
    |>.header! "X-Content-Type-Options" "nosniff"
    |>.header! "Referrer-Policy" "no-referrer"
    |>.header! "Cache-Control" "no-store"
    |>.fromBytes body
  return r

/-- A JSON response. -/
def replyJson (status : Status) (body : String) : ContextAsync (Response Body.Any) :=
  reply status "application/json" body.toUTF8

/-- A plain text response. -/
def replyText (status : Status) (body : String) : ContextAsync (Response Body.Any) :=
  reply status "text/plain; charset=utf-8" body.toUTF8

/-! ## Static files -/

/-- The content type for a file name, by its extension. `none` means the server does not serve it. -/
def contentType (name : String) : Option String :=
  match (name.splitOn ".").getLast? with
  | some "html" => some "text/html; charset=utf-8"
  | some "css" => some "text/css; charset=utf-8"
  | some "js" => some "text/javascript; charset=utf-8"
  | some "svg" => some "image/svg+xml"
  | some "png" => some "image/png"
  | some "ico" => some "image/x-icon"
  | _ => none

/-- Serve a file from the folder `root`, or 404 if the path is not safe or the file is missing. -/
def serveStatic (root : System.FilePath) (segments : List String) :
    ContextAsync (Response Body.Any) := do
  let segments := if segments.isEmpty || segments == [""] then ["index.html"] else segments
  let some name := segments.getLast? | replyText .notFound "not found"
  let some ctype := contentType name | replyText .notFound "not found"
  if !segments.all safeSegment then
    replyText .notFound "not found"
  else
    let path := segments.foldl (· / ·) root
    if !(← path.pathExists) || (← path.isDir) then
      replyText .notFound "not found"
    else
      let bytes ← IO.FS.readBinFile path
      reply .ok ctype bytes

/-- Serve a Picture of the saved Adventure in play. Only a Picture that passed the check is served.
The same guards as `serveStatic` apply: safe segments and the SVG content type only. -/
def servePicture (s : ServerState) (id file : String) : ContextAsync (Response Body.Any) := do
  let name := file.dropSuffix ".svg" |>.toString
  if s.source.savedId != some id || !file.endsWith ".svg" || !s.source.pictures.contains name ||
      !safeSegment id || !safeSegment file || !safePicture name then
    replyText .notFound "not found"
  else
    serveStatic (savedRoot / id) [file]

/-! ## Router -/

/-- The largest request body the server reads, in bytes. -/
def maxBody : UInt64 := 4096

/-- The most characters in a Wish. -/
def maxWish : Nat := 500

/-- The most characters in the Character's name from the Player. -/
def maxName : Nat := 30

/-- A new seed for a new game. -/
def freshSeed : IO Nat := do
  return (← IO.monoNanosNow) % 1000000

/-- The media type of a `Content-Type` value, in lowercase, such as "application/json". -/
def mediaType (value : String) : String :=
  ((value.splitOn ";").headD "").trimAscii.toString.toLower

/-- A POST may change the game only if it says its body is JSON, and, if it names an `Origin`,
that origin is this server's own page. Another website in the Player's browser can send a POST
with a plain-text body and no preflight check, but not a JSON one; and the browser always names
the `Origin` of such a request. -/
def postAllowed (host : String) (port : Nat) (headers : Headers) : Bool :=
  let isJson := match headers.getAll? Header.Name.contentType with
    | some #[v] => mediaType (toString v) == "application/json"
    | _ => false
  let ours := [s!"http://{host}:{port}", s!"http://127.0.0.1:{port}", s!"http://localhost:{port}"]
  let originOk := match headers.getAll? Header.Name.origin with
    | none => true
    | some vs => vs.all fun v => ours.contains (toString v)
  isJson && originOk

/-- Read a Wish from a request body. Returns the Wish, the name, and the gender, or an error. -/
def parseWish (body : String) : Except String (String × String × String) := do
  let j ← Json.parse body
  let wish := (j.getObjValAs? String "wish").toOption.getD "" |>.trimAscii.toString
  let name := (j.getObjValAs? String "name").toOption.getD "" |>.trimAscii.toString
  let gender := (j.getObjValAs? String "gender").toOption.getD "dm"
  if wish.isEmpty then throw "Type a Wish first."
  if wish.length > maxWish then throw s!"A Wish can have at most {maxWish} characters."
  if name.length > maxName then throw s!"A name can have at most {maxName} characters."
  if !["she", "he", "they", "dm"].contains gender then throw "Pick she, he, they, or let the DM choose."
  return (wish, name, gender)

#guard (parseWish "{\"wish\": \"the Shire\", \"name\": \"Pip\", \"gender\": \"he\"}").toOption == some ("the Shire", "Pip", "he")
#guard (parseWish "{\"wish\": \"  \"}").toOption.isNone
#guard (parseWish ("{\"wish\": \"" ++ "".pushn 'a' 501 ++ "\"}")).toOption.isNone

/-- Load a saved Adventure: read it, check it again, and check its Pictures again. -/
def loadSaved (id : String) : IO (Except String (Game × Source × Draft)) := do
  if !safeSegment id then return .error "There is no saved Adventure with that name."
  let path := savedRoot / id / "adventure.json"
  if !(← path.pathExists) then return .error "There is no saved Adventure with that name."
  let text ← IO.FS.readFile path
  match checkSavedText text with
  | .error errs => return .error s!"The saved Adventure failed the check: {"; ".intercalate errs}"
  | .ok (d, g) =>
      let pictures ← checkedPictures id d.adventure
      return .ok (g, { savedId := some id, background := some d.background, pictures }, d)

/-- Change the server state with `f`, but only if the DM is not writing. The check and the change
are one atomic step, so a Wish that finishes in between is never overwritten. Returns `none`, and
changes nothing, if the DM is writing. -/
def whenIdle (ref : IO.Ref ServerState) (f : ServerState → α × ServerState) : IO (Option α) :=
  ref.modifyGet fun s =>
    if s.gen.state == .running then (none, s) else
    let (a, s') := f s
    (some a, s')

/-- Stop the Picture work of the saved Adventure that was in play, if another one is in play now. -/
def stopOldPictures (children : Children) (old new : Option String) : IO Unit := do
  if let some oldId := old then
    if new != some oldId then killOwner children (picturesOwner oldId)

/-- Answer one request. -/
def route (cfg : GameConfig) (webRoot : System.FilePath) (children : Children)
    (state : IO.Ref ServerState) (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  let segments := (req.line.uri.path.segments.map toString).toList
  let method := req.line.method
  if method == .post && !postAllowed cfg.host cfg.port req.line.headers then
    return ← replyText .forbidden "forbidden: a POST must be JSON from this page"
  let view (fresh : Nat := 0) (error : Option String := none) : ContextAsync String := do
    fullView cfg (← state.get) fresh error
  match method, segments with
  | .get, ["api", "view"] =>
    replyJson .ok (← view)
  | .get, ["saved", id, file] =>
    servePicture (← state.get) id file
  | .post, path =>
    -- `readAll` throws when the body is larger than `maxBody`.
    let body? : Option String ←
      try pure (some (← req.body.readAll (maximumSize := some maxBody)))
      catch _ => pure none
    let some body := body?
      | replyText .payloadTooLarge "request body too large"
    if path == ["api", "cancel"] then
      cancelWish children state
      return ← replyJson .ok (← view)
    let busyMsg := "The DM is still writing. Wait, or click Cancel."
    let busy : ContextAsync (Response Body.Any) := do
      replyJson .conflict (← view (error := some busyMsg))
    -- A quick check first. Each change below checks again, atomically (`whenIdle`).
    if (← state.get).gen.state == .running then
      return ← busy
    match path with
    | ["api", "input"] =>
      match Json.parse body >>= fromJson? (α := Input) with
      | .error e =>
        replyJson .badRequest (← view (error := some s!"Bad input: {e}"))
      | .ok i =>
        let r ← whenIdle state fun s =>
          let (s', error, fresh) := s.session.apply i
          ((error, fresh), { s with session := s' })
        match r with
        | none => busy
        | some (some why, _) => replyJson .badRequest (← view (error := some why))
        | some (none, fresh) => replyJson .ok (← view fresh)
    | ["api", "new"] =>
      let seed ← freshSeed
      let r ← whenIdle state fun s => ((), { s with session := Session.start s.session.fresh seed })
      if r.isNone then return ← busy
      replyJson .ok (← view)
    | ["api", "builtin"] =>
      let seed ← freshSeed
      let r ← whenIdle state fun s =>
        (s.source.savedId, { s with session := Session.start builtinGame seed, source := {},
                                    gen := { s.gen with state := .idle, steps := #[] } })
      let some old := r | busy
      stopOldPictures children old none
      replyJson .ok (← view)
    | ["api", "dismiss"] =>
      let r ← whenIdle state fun s => ((), { s with gen := { s.gen with state := .idle, steps := #[] } })
      if r.isNone then return ← busy
      replyJson .ok (← view)
    | ["api", "wish"] =>
      if !cfg.canWish then
        return ← replyJson .badRequest (← view (error := some "Generation is unavailable: no API key."))
      match parseWish body with
      | .error e => replyJson .badRequest (← view (error := some e))
      | .ok (wish, name, gender) =>
        if !(← startWish cfg children state wish name gender) then return ← busy
        replyJson .ok (← view)
    | ["api", "retry"] =>
      let g := (← state.get).gen
      if !cfg.canWish || g.wish.isEmpty then
        return ← replyJson .badRequest (← view (error := some "There is no Wish to try again."))
      if !(← startWish cfg children state g.wish g.name g.gender) then return ← busy
      replyJson .ok (← view)
    | ["api", "load"] =>
      let id := (Json.parse body >>= (·.getObjValAs? String "id")).toOption.getD ""
      match ← loadSaved id with
      | .error e =>
        -- The list shows this refusal too, until the file changes.
        if safeSegment id then markRefused cfg id e
        replyJson .badRequest (← view (error := some e))
      | .ok (g, src, d) =>
        let seed ← freshSeed
        -- Pictures with no file and no refusal on record are drawn now (if the DM can be asked).
        let missing ← if cfg.canWish && cfg.picturesOn then missingPictures id d.adventure else pure []
        -- Loading the Adventure that is already in play, while its Pictures are drawing, keeps
        -- that drawing run and its lists. Otherwise a new run draws the missing Pictures.
        let r ← whenIdle state fun s =>
          let keep := s.source.savedId == some id && !s.source.drawing.isEmpty
          let run := s.runs + 1
          let source := if keep then s.source else
            { src with drawing := missing.filterMap (·.picture), drawRun := run }
          let gen := { s.gen with state := .idle, steps := #[] }
          ((s.source.savedId, keep, run),
            { s with session := Session.start g seed, source, gen, runs := if keep then s.runs else run })
        let some (old, keep, run) := r | busy
        stopOldPictures children old (some id)
        -- Old runs of this Adventure are no longer current, so their draft folders can go.
        if !keep then cleanDraftFolders id
        if !keep && !missing.isEmpty then
          let _ ← IO.asTask (drawPictures cfg children state id run d missing) .dedicated
        replyJson .ok (← view)
    | _ => replyText .notFound "not found"
  | .get, "api" :: _ => replyText .notFound "not found"
  | .get, "saved" :: _ => replyText .notFound "not found"
  | .get, _ => serveStatic webRoot segments
  | _, _ => replyText .methodNotAllowed "method not allowed"

/-! ## Start -/

/-- Read `--name N` from the command line. -/
def natArg (name : String) : List String → Option Nat
  | n :: v :: rest => if n == name then v.toNat? else natArg name (v :: rest)
  | _ => none

/-- Read `--name VALUE` from the command line. -/
def stringArg (name : String) : List String → Option String
  | n :: v :: rest => if n == name then some v else stringArg name (v :: rest)
  | _ => none

/-- Read an IPv4 address such as "10.211.55.6". Each of the four parts must be from 0 to 255. -/
def parseIPv4 (s : String) : Option Net.IPv4Addr :=
  match (s.splitOn ".").map String.toNat? with
  | [some a, some b, some c, some d] =>
    if a < 256 ∧ b < 256 ∧ c < 256 ∧ d < 256 then
      some (.ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8)
    else none
  | _ => none

#guard (parseIPv4 "10.211.55.6").isSome
#guard (parseIPv4 "10.211.55").isNone
#guard (parseIPv4 "10.211.55.256").isNone

/-- Check the Adventure, then serve the game until Ctrl-C. Options: `--seed N` for the first
game, `--port N` (default 8080), `--host A.B.C.D` (default 127.0.0.1). The environment variable
`ANTHROPIC_API_KEY` turns on Wishes. `RPG_FAKE_API=<folder>` is a test hook: the server reads
recorded API replies from the folder and never calls the API. -/
def main (args : List String) : IO UInt32 := do
  -- Check the Adventure again, on the value the program will play.
  -- The theorem covers the value Lean proved things about. A trick such as `implemented_by`
  -- can make the compiled value different, and this check catches that.
  let errs := checkCharacter Lighthouse.rules Lighthouse.mara ++
    check Lighthouse.rules Lighthouse.mara Lighthouse.lighthouse
  if !errs.isEmpty then
    IO.eprintln "The Adventure failed the check, so the game will not start:"
    for e in errs do IO.eprintln s!"  ERROR: {e}"
    return 1
  -- The built-in Adventure must also pass the fairness check, with the fixed validation seed.
  let (counts, admitted) := Probability.admitStatistically Lighthouse.statisticalCandidate
  if admitted.isNone then
    IO.eprintln "The Adventure failed the fairness check, so the game will not start:"
    for e in Probability.failedRows Lighthouse.statisticalCandidate.horizon counts do
      IO.eprintln s!"  ERROR: {e}"
    return 1
  let webRoot : System.FilePath := "web"
  if !(← (webRoot / "index.html").pathExists) then
    IO.eprintln "Cannot find web/index.html. Run the server from the repository folder."
    return 1
  let seed ← match natArg "--seed" args with
    | some s => pure s
    | none => freshSeed
  let port := (natArg "--port" args).getD 8080
  let host := (stringArg "--host" args).getD "127.0.0.1"
  let some ip := parseIPv4 host
    | IO.eprintln s!"--host must be an IPv4 address such as 10.0.0.5, not {host}."
      return 1
  -- The Picture check must run for live Pictures. If it cannot, Pictures are off: say so once,
  -- clearly, and never ask the DM for a Picture.
  let picturesOn := (← runPictureCheck #["web/pictures"]) != .cannotCheck
  if !picturesOn then
    IO.eprintln ("WARNING: scripts/check_pictures.py cannot run (is python3 installed?). " ++
      "Pictures are off: live Adventures show a plain backdrop, and the DM is not asked to draw.")
  let apiKey := (← IO.getEnv "ANTHROPIC_API_KEY").filter (!·.isEmpty)
  let fake := (← IO.getEnv "RPG_FAKE_API").filter (!·.isEmpty) |>.map System.FilePath.mk
  let cfg : GameConfig := { host, port, apiKey, fake, savedCache := ← IO.mkRef [], picturesOn }
  let state ← IO.mkRef ({ session := Session.start builtinGame seed } : ServerState)
  let children ← IO.mkRef #[]
  let addr : Net.SocketAddress := .v4 ⟨ip, port.toUInt16⟩
  Async.block do
    let server ← Server.serve addr (Handler.ofFn (route cfg webRoot children state))
    IO.println s!"The game is ready at http://{host}:{port}/ (first seed {seed})."
    if let some dir := fake then
      IO.println s!"TEST MODE: Wishes read recorded replies from {dir}. The API is not called."
    else if apiKey.isNone then
      IO.println "No ANTHROPIC_API_KEY is set, so Wishes are off. The built-in Adventure works."
    IO.println "Press Ctrl-C to stop."
    (← IO.getStdout).flush
    server.waitShutdown
  return 0
