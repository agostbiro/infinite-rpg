import Rpg.View
import Std.Http

/-!
# Game server

This program serves the game to a browser with core `Std.Http`. By default it listens on
`localhost` (127.0.0.1) only. `--host A.B.C.D` makes it listen on that IPv4 (Internet Protocol
version 4) address instead, for example to play from the host of a VM (virtual machine).
It keeps one game in memory. The page draws the view that the server sends,
and sends back the Player's inputs. All rules and dice stay in Lean (`Rpg.step`).

Routes:

* `GET /api/view`: the current view.
* `POST /api/input`: apply one input (JSON). A refused input gives status 400, an error, and the
  view, and changes nothing.
* `POST /api/new`: start a new game with a new seed.
* `GET /<file>`: a file from `web/`. `/` is `web/index.html`.

Every POST must have `Content-Type: application/json`, and its `Origin`, if any, must be this
server. Else the reply is 403. This stops other websites in the Player's browser from driving
the game. A body over 4 KB gets 413.

This code has no proofs. The proofs are about `Rpg.step`, which this code calls.
-/

open Std Async Http Server
open Lean (Json toJson fromJson?)
open Rpg

/-- The one game the server keeps, with its dice and every Report since it began. -/
structure Session where
  game : Game
  dice : Rng
  seed : Nat
  reports : Array Report

/-- A new game of The Drowned Lighthouse for Mara, on the title screen. -/
def Session.new (seed : Nat) : Session :=
  { game := Game.new mara lighthouse, dice := ⟨seed.toUInt64⟩, seed, reports := #[] }

/-- The view of a session. `fresh` is the number of new Reports at the end. -/
def Session.view (s : Session) (fresh : Nat := 0) (error : Option String := none) : String :=
  (viewJson s.game s.seed s.reports fresh error).compress

/-- Apply one input. Returns the new session, or the reason the input was refused.
A refused input leaves the session as it was. -/
def Session.apply (s : Session) (i : Input) : Session × Option String × Nat :=
  let ((g, reports), dice) := (step s.game i).run s.dice
  match reports.find? (·.isRejected) with
  | some (.rejected why) => (s, some why, 0)
  | _ => ({ s with game := g, dice, reports := s.reports ++ reports.toArray }, none, reports.length)

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

/-- A path segment is safe if it has only letters, digits, `-`, `_`, and `.`, and does not start
with `.`. So `..`, hidden files, and encoded characters such as `%2e` are refused. -/
def safeSegment (seg : String) : Bool :=
  !seg.isEmpty && !seg.startsWith "." &&
    seg.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- Serve a file from the `web` folder, or 404 if the path is not safe or the file is missing. -/
def serveStatic (webRoot : System.FilePath) (segments : List String) :
    ContextAsync (Response Body.Any) := do
  let segments := if segments.isEmpty || segments == [""] then ["index.html"] else segments
  let some name := segments.getLast? | replyText .notFound "not found"
  let some ctype := contentType name | replyText .notFound "not found"
  if !segments.all safeSegment then
    replyText .notFound "not found"
  else
    let path := segments.foldl (· / ·) webRoot
    if !(← path.pathExists) || (← path.isDir) then
      replyText .notFound "not found"
    else
      let bytes ← IO.FS.readBinFile path
      reply .ok ctype bytes

/-! ## Router -/

/-- The largest request body the server reads, in bytes. -/
def maxBody : UInt64 := 4096

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

/-- Answer one request. -/
def route (webRoot : System.FilePath) (host : String) (port : Nat) (state : IO.Ref Session)
    (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  let segments := (req.line.uri.path.segments.map toString).toList
  let method := req.line.method
  if method == .post && !postAllowed host port req.line.headers then
    return ← replyText .forbidden "forbidden: a POST must be JSON from this page"
  match method, segments with
  | .get, ["api", "view"] =>
    replyJson .ok (← state.get).view
  | .post, ["api", "input"] =>
    -- `readAll` throws when the body is larger than `maxBody`.
    let body? : Option String ←
      try pure (some (← req.body.readAll (maximumSize := some maxBody)))
      catch _ => pure none
    let some body := body?
      | replyText .payloadTooLarge "request body too large"
    match Json.parse body >>= fromJson? (α := Input) with
    | .error e =>
      replyJson .badRequest ((← state.get).view (error := some s!"Bad input: {e}"))
    | .ok i =>
      let (s, error, fresh) ← state.modifyGet fun s =>
        let (s', error, fresh) := s.apply i
        ((s', error, fresh), s')
      match error with
      | some why => replyJson .badRequest (s.view (error := some why))
      | none => replyJson .ok (s.view fresh)
  | .post, ["api", "new"] =>
    let seed ← freshSeed
    let s := Session.new seed
    state.set s
    replyJson .ok s.view
  | .get, "api" :: _ => replyText .notFound "not found"
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
game, `--port N` (default 8080), `--host A.B.C.D` (default 127.0.0.1). -/
def main (args : List String) : IO UInt32 := do
  -- Check the Adventure again, on the value the program will play.
  -- The theorem covers the value Lean proved things about. A trick such as `implemented_by`
  -- can make the compiled value different, and this check catches that.
  let errs := checkCharacter mara ++ check mara lighthouse
  if !errs.isEmpty then
    IO.eprintln "The Adventure failed the check, so the game will not start:"
    for e in errs do IO.eprintln s!"  ERROR: {e}"
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
  let state ← IO.mkRef (Session.new seed)
  let addr : Net.SocketAddress := .v4 ⟨ip, port.toUInt16⟩
  Async.block do
    let server ← Server.serve addr (Handler.ofFn (route webRoot host port state))
    IO.println s!"The Drowned Lighthouse is ready at http://{host}:{port}/ (first seed {seed})."
    IO.println "Press Ctrl-C to stop."
    (← IO.getStdout).flush
    server.waitShutdown
  return 0
