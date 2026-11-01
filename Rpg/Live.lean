import Rpg.View
import Rpg.EventGraph
import Rpg.Probability.StatisticalAdmission
import Rpg.Environment

/-!
# Live Adventures

The Player types a Wish, and the DM (an LLM, large language model) sends back an Adventure and a
Character as JSON (JavaScript Object Notation). This file reads that JSON into a `Draft` and turns
a `Draft` into a `Game`.

`Draft.toGame` is the only way in this code from a Draft to a Game. This holds by convention, not
by type: `Game.new` is public, and the server calls only `Draft.toGame`. It runs the proved checker on the
Character and on the Adventure. A `Game` needs the proofs `LegalCharacter` and `LegalAdventure`
(see `Game.new`), and `Draft.toGame` gets them only from `checkCharacter_sound` and `check_sound`.
So a Draft that the checker rejects can never be played.

Then `Draft.toGame` runs the balance check (admission): `difficultyGames` games from a seed, with
horizon 5, against the curve of the Draft's difficulty level. A Draft that fails a row is not
played either. The server picks a fresh random seed for each try and saves it with the Adventure,
so a saved Adventure gives the same result when it loads.
A Wish uses the default rules (`liveRules`). The DM cannot change them.
The Player picks the level. The server sets it on the Draft, so the DM cannot change it either.

Before the checker runs, `sizeErrors` refuses a Draft that is too large to show well, for
example more than 40 Scenes, and a world map that the 3D page cannot draw
(`WorldEnvironment.errors`). These limits are not part of the spec.

The JSON here has no proofs. A wrong decoder can only give the checker a different Adventure,
and the checker then checks that Adventure.
-/

namespace Rpg

open Lean

/-! ## Names of rule things in JSON -/

/-- The JSON name of a skill, such as "firstAid". -/
def Skill.key : Skill → String
  | .broadsword => "broadsword"
  | .knife => "knife"
  | .brawling => "brawling"
  | .stealth => "stealth"
  | .lockpicking => "lockpicking"
  | .diplomacy => "diplomacy"
  | .survival => "survival"
  | .naturalist => "naturalist"
  | .occultism => "occultism"
  | .riding => "riding"
  | .climbing => "climbing"
  | .swimming => "swimming"
  | .firstAid => "firstAid"
  | .fastTalk => "fastTalk"
  | .staff => "staff"
  | .liquidProjector => "liquidProjector"

/-- The JSON name of a weapon, such as "largeKnife". -/
def Weapon.key : Weapon → String
  | .broadsword => "broadsword"
  | .largeKnife => "largeKnife"
  | .punch => "punch"
  | .quarterstaff => "quarterstaff"
  | .flamethrower => "flamethrower"

/-- The JSON name of a type of armor. -/
def Armor.key : Armor → String
  | .none => "none"
  | .leather => "leather"

/-- Every attribute, in a fixed order. -/
def Attribute.all : List Attribute := [.st, .dx, .iq, .ht]

/-- The JSON name of a roll target: a skill name, or "ST", "DX", "IQ", or "HT". -/
def RollTarget.key : RollTarget → String
  | .skill s => s.key
  | .attribute a => a.name

/-- Every roll target: each skill, then each attribute. -/
def RollTarget.all : List RollTarget :=
  Skill.all.map .skill ++ Attribute.all.map .attribute

/-- Find the thing in `all` with the JSON name `k`. -/
def ofKey? (all : List α) (key : α → String) (what k : String) : Except String α :=
  match all.find? (key · == k) with
  | some x => .ok x
  | none => .error s!"\"{k}\" is not a {what}. Use one of: {", ".intercalate (all.map key)}"

-- Each JSON name names one thing.
#guard (Skill.all.map Skill.key).eraseDups.length == Skill.all.length
#guard (RollTarget.all.map RollTarget.key).eraseDups.length == RollTarget.all.length

/-! ## A Draft: what the DM sends -/

/-- What the DM sends for a Wish: an Adventure, its Character, and things only the Player sees. -/
structure Draft where
  /-- The Adventure, with its Theme Names. -/
  adventure : Adventure
  /-- The Character. -/
  hero : Being
  /-- A short story of the Character, for the Character panel. -/
  background : String
  /-- The World of the Adventure in a few words, such as "Middle-earth, the Shire". An older save
  has none: then it is empty. -/
  world : String := ""
  /-- The Intro: the text the Player reads before the first Scene. An older save has none: then it
  is empty. -/
  intro : String := ""
  /-- The world map for the 3D page. An older save has none: then the page draws a default map. -/
  environment : Option WorldEnvironment := none
  /-- The difficulty level that the Player picked. An older save has none: then it is medium. -/
  difficulty : Probability.DifficultyLevel := .medium
  deriving Repr

/-- Add a context, such as "Scene 3", to the front of an error. -/
def inCtx (ctx : String) : Except String α → Except String α
  | .ok x => .ok x
  | .error e => .error s!"{ctx}: {e}"

/-- Read a list from field `k` of an object, with `f` for each entry. -/
def listField (j : Json) (k : String) (f : Json → Except String α) : Except String (List α) := do
  let arr ← inCtx k (j.getObjVal? k >>= Json.getArr?)
  let mut out := []
  for (x, i) in arr.toList.zipIdx do
    out := out ++ [← inCtx s!"{k} {i + 1}" (f x)]
  return out

/-- Read a learned skill: `{"skill": "stealth", "level": 12}`. -/
def skillOfJson (j : Json) : Except String (Skill × Nat) := do
  let s ← ofKey? Skill.all Skill.key "skill" (← j.getObjValAs? String "skill")
  let l ← inCtx "level" (j.getObjValAs? Nat "level")
  return (s, l)

/-- Read a being. The Character has no `naturalDR` field; then natural DR is 0. -/
def beingOfJson (j : Json) : Except String Being := do
  let name ← j.getObjValAs? String "name"
  inCtx name do
    let st ← inCtx "st" (j.getObjValAs? Nat "st")
    let dx ← inCtx "dx" (j.getObjValAs? Nat "dx")
    let iq ← inCtx "iq" (j.getObjValAs? Nat "iq")
    let ht ← inCtx "ht" (j.getObjValAs? Nat "ht")
    let skills ← listField j "skills" skillOfJson
    let weapon ← ofKey? Weapon.all Weapon.key "weapon" (← j.getObjValAs? String "weapon")
    let armor ← ofKey? Armor.all Armor.key "armor" (← j.getObjValAs? String "armor")
    let naturalDR ← match j.getObjVal? "naturalDR" with
      | .ok v => inCtx "naturalDR" (fromJson? v)
      | .error _ => pure 0
    return { name, st, dx, iq, ht, skills, weapon, armor, naturalDR }

/-- Read an Outcome: a `goto`, a `roll`, or a `fight`, named by its `type` field. -/
def outcomeOfJson (j : Json) : Except String Outcome := do
  match ← j.getObjValAs? String "type" with
  | "goto" => return .goto (← j.getObjValAs? Nat "next")
  | "roll" =>
    let t ← ofKey? RollTarget.all RollTarget.key "roll target" (← j.getObjValAs? String "against")
    return .roll t (← j.getObjValAs? Int "modifier") (← j.getObjValAs? Nat "onSuccess")
      (← j.getObjValAs? Nat "onFailure")
  | "fight" => return .fight (← listField j "foes" beingOfJson) (← j.getObjValAs? Nat "onWin")
  | t => throw s!"type \"{t}\" is not goto, roll, or fight"

/-- Read a Choice. -/
def choiceOfJson (j : Json) : Except String Choice := do
  return { text := ← j.getObjValAs? String "text", outcome := ← inCtx "outcome" (outcomeOfJson (← j.getObjVal? "outcome")) }

/-- Read a Scene. -/
def sceneOfJson (j : Json) : Except String Scene := do
  let id ← j.getObjValAs? Nat "id"
  inCtx s!"Scene {id}" do
    return { id, title := ← j.getObjValAs? String "title", text := ← j.getObjValAs? String "text",
             choices := ← listField j "choices" choiceOfJson }

/-- Read a list from field `k` of an object, or the empty list if there is no such field. -/
def optListField (j : Json) (k : String) (f : Json → Except String α) : Except String (List α) :=
  match j.getObjVal? k with
  | .ok _ => listField j k f
  | .error _ => pure []

/-- Read the Theme Names. Each list is optional. -/
def themesOfJson (j : Json) : Except String ThemeNames := do
  let skills ← optListField j "skills" fun x => do
    return (← ofKey? Skill.all Skill.key "skill" (← x.getObjValAs? String "skill"), ← x.getObjValAs? String "name")
  let weapons ← optListField j "weapons" fun x => do
    return (← ofKey? Weapon.all Weapon.key "weapon" (← x.getObjValAs? String "weapon"), ← x.getObjValAs? String "name")
  let armor ← optListField j "armor" fun x => do
    return (← ofKey? Armor.all Armor.key "armor" (← x.getObjValAs? String "armor"), ← x.getObjValAs? String "name")
  return { skills, weapons, armor }

/-- Read the string field `k` of an object, or the empty string if there is no such field. -/
def optStrField (j : Json) (k : String) : Except String String :=
  match j.getObjVal? k with
  | .ok v => inCtx k (fromJson? v)
  | .error _ => pure ""

/-- Read the difficulty level from field `difficulty`. A missing field is medium. A field that
is not "easy", "medium", or "hard" is an error. -/
def difficultyOfJson (j : Json) : Except String Probability.DifficultyLevel :=
  match j.getObjVal? "difficulty" with
  | .error _ => pure .medium
  | .ok v => do
    let key ← inCtx "difficulty" (fromJson? (α := String) v)
    match Probability.DifficultyLevel.ofKey? key with
    | some level => pure level
    | none => throw s!"difficulty: \"{key}\" is not easy, medium, or hard"

/-- Read a Draft from the DM's JSON. -/
def Draft.ofJson (j : Json) : Except String Draft := do
  let title ← j.getObjValAs? String "title"
  let world ← optStrField j "world"
  let intro ← optStrField j "intro"
  let start ← j.getObjValAs? Nat "start"
  let scenes ← listField j "scenes" sceneOfJson
  let themes ← match j.getObjVal? "themeNames" with
    | .ok t => inCtx "themeNames" (themesOfJson t)
    | .error _ => pure {}
  let c ← inCtx "character" (j.getObjVal? "character")
  let hero ← inCtx "character" (beingOfJson c)
  let background ← inCtx "character" (c.getObjValAs? String "background")
  let environment ← match j.getObjVal? "environment" with
    | .ok v => inCtx "environment" (fromJson? v : Except String (Option WorldEnvironment))
    | .error _ => pure none
  let difficulty ← difficultyOfJson j
  return { adventure := { title, start, scenes, themes }, hero, background, world, intro, environment,
           difficulty }

/-- Read a Draft from JSON text. -/
def Draft.parse (s : String) : Except String Draft := do
  Draft.ofJson (← Json.parse s)

/-! ## Writing a Draft back to JSON, for saving -/

/-- A learned skill as JSON. -/
def skillToJson (e : Skill × Nat) : Json := json% { skill: $(e.1.key), level: $(e.2) }

/-- A being as JSON. -/
def beingToJson (b : Being) : Json :=
  json% {
    name: $(b.name), st: $(b.st), dx: $(b.dx), iq: $(b.iq), ht: $(b.ht),
    skills: $(b.skills.map skillToJson), weapon: $(b.weapon.key), armor: $(b.armor.key),
    naturalDR: $(b.naturalDR)
  }

/-- An Outcome as JSON. -/
def outcomeToJson : Outcome → Json
  | .goto n => json% { type: "goto", next: $(n) }
  | .roll t m s f => json% { type: "roll", against: $(t.key), modifier: $(m), onSuccess: $(s), onFailure: $(f) }
  | .fight foes w => json% { type: "fight", foes: $(foes.map beingToJson), onWin: $(w) }

/-- A Draft as JSON, in the same form that `Draft.ofJson` reads. A Draft with no world map has no
`environment` field. -/
def Draft.toJson (d : Draft) : Json :=
  let a := d.adventure
  let th := a.themes
  let j := json% {
    title: $(a.title),
    difficulty: $(d.difficulty.key),
    world: $(d.world),
    intro: $(d.intro),
    character: $((beingToJson d.hero).setObjVal! "background" (Json.str d.background)),
    themeNames: {
      skills: $(th.skills.map fun (s, n) => json% { skill: $(s.key), name: $(n) }),
      weapons: $(th.weapons.map fun (w, n) => json% { weapon: $(w.key), name: $(n) }),
      armor: $(th.armor.map fun (x, n) => json% { armor: $(x.key), name: $(n) })
    },
    start: $(a.start),
    scenes: $(a.scenes.map fun sc => json% {
      id: $(sc.id), title: $(sc.title), text: $(sc.text),
      choices: $(sc.choices.map fun ch => json% { text: $(ch.text), outcome: $(outcomeToJson ch.outcome) })
    })
  }
  match d.environment with
  | some e => j.setObjVal! "environment" (Lean.toJson e)
  | none => j

/-! ## Size limits

These limits keep a Draft small enough to show and to save. They are not part of the spec:
the checker and the theorems do not depend on them. -/

/-- The most Scenes a live Adventure may have. -/
def maxScenes : Nat := 40

/-- The most characters in the text of one Scene. -/
def maxSceneText : Nat := 2000

/-- The most characters in a title, a Choice, a name, or a Theme Name. -/
def maxShortText : Nat := 120

/-- The most characters in the Character's background. -/
def maxBackground : Nat := 1000

/-- The most characters in the World. -/
def maxWorld : Nat := 60

/-- The most characters in the Intro. -/
def maxIntro : Nat := 600

/-- An error if `s` has more than `n` characters. -/
def tooLong (what : String) (n : Nat) (s : String) : List String :=
  if s.length > n then [s!"{what} has {s.length} characters, but the limit is {n}"] else []

/-- The names of all the beings in a Draft. -/
def Draft.beingNames (d : Draft) : List String :=
  d.hero.name :: d.adventure.scenes.flatMap fun sc =>
    sc.choices.flatMap fun ch => ch.outcome.foes.map (·.name)

/-- Errors for a Draft that is too large. The checker runs only if there are none. -/
def sizeErrors (d : Draft) : List String :=
  let a := d.adventure
  let th := a.themes
  (match d.environment with
    | some e => e.errors a
    | none => []) ++
  (if a.scenes.length > maxScenes then
    [s!"the Adventure has {a.scenes.length} Scenes, but the limit is {maxScenes}"] else []) ++
  tooLong "the title" maxShortText a.title ++
  tooLong "the background" maxBackground d.background ++
  tooLong "the world" maxWorld d.world ++
  tooLong "the intro" maxIntro d.intro ++
  a.scenes.flatMap (fun sc =>
    tooLong s!"the text of Scene {sc.id}" maxSceneText sc.text ++
    tooLong s!"the title of Scene {sc.id}" maxShortText sc.title ++
    sc.choices.flatMap fun ch => tooLong s!"a Choice in Scene {sc.id}" maxShortText ch.text) ++
  d.beingNames.flatMap (fun n => tooLong s!"the name \"{n.take 20}...\"" maxShortText n) ++
  (th.skills.map (·.2) ++ th.weapons.map (·.2) ++ th.armor.map (·.2)).flatMap
    (tooLong "a Theme Name" maxShortText)

/-! ## From a Draft to a Game -/

/-- The rules of every Wish: the default rules. -/
def liveRules : RuleSet := {}

/-- The number of turns that the balance check covers for a Wish, after the first one. -/
def liveHorizon : Nat := 5

/-- All errors in a Draft: the size errors, or else the checker's errors for the Character and
for the Adventure, and the short loops (see `Adventure.noShortLoops`). An empty list means the
Draft passes the checker. -/
def Draft.errors (d : Draft) : List String :=
  match sizeErrors d with
  | [] => checkCharacter liveRules d.hero ++ check liveRules d.hero d.adventure ++
      d.adventure.shortLoopErrors
  | errs => errs

/-- Run the size limits, the short-loop check and the checker on a Draft. If all find no errors,
the soundness theorems give the proofs that an `AdventureDefinition` needs. Else it returns the
errors. -/
private def Draft.checked (d : Draft) : Except (List String) AdventureDefinition :=
  if sizeErrors d ≠ [] then .error (sizeErrors d) else
  if hc : checkCharacter liveRules d.hero = [] then
    if ha : check liveRules d.hero d.adventure = [] then
      if d.adventure.checkShortLoops then
        .ok ⟨liveRules, d.hero, checkCharacter_sound hc, d.adventure, check_sound ha⟩
      else .error d.adventure.shortLoopErrors
    else .error (check liveRules d.hero d.adventure ++ d.adventure.shortLoopErrors)
  else .error (checkCharacter liveRules d.hero ++ check liveRules d.hero d.adventure ++
    d.adventure.shortLoopErrors)

/-- A Draft that passed the checker, as a candidate for the balance check with `policy`. -/
def liveCandidate (defn : AdventureDefinition) (policy : Probability.BalancePolicy) :
    Probability.StatisticalCandidate :=
  Probability.StatisticalCandidate.atCheckpoint defn
    (.scene defn.story.start (defn.rules.maxHP defn.hero)) 0 liveHorizon (by decide) policy

/-- A Game from a Draft that this build of the server already admitted: it runs the size limits and
the checker again, but not the balance check. Use it only when a saved verdict for this exact
text and this build says that the Draft passed both checks (see `loadSaved` in `Main.lean`).
The Game gets the policy of the Draft's level. -/
def Draft.toGameAdmitted (d : Draft) : Except (List String) Game :=
  d.checked.map (Game.new · d.difficulty.policy)

/-- **The only way in this code from a Draft to a Game that runs the balance check.** It runs the
checker, then the balance check with `difficultyGames` games from `seed`, against the curve of the
Draft's level. If both pass, it returns the Game, with that policy. Else it returns the errors.
Each balance error starts with "balance:" and names the row that failed. -/
def Draft.toGame (d : Draft) (seed : Nat) : Except (List String) Game :=
  match d.checked with
  | .error errs => .error errs
  | .ok defn =>
    match Probability.admitWithSeed (liveCandidate defn d.difficulty.policy) seed with
    | (_, some a) => .ok (Game.new a.candidate.toAdventureDefinition a.candidate.policy)
    | (counts, none) =>
      .error (((liveCandidate defn d.difficulty.policy).failures counts Probability.Confidence.confidenceDelta).map ("balance: " ++ ·))

/-- How the points of a being add up, such as "ST 11: 10, DX 12: 40, ... Total: 100". The DM
gets this with the errors, so it can fix a build. -/
def pointsBreakdown (b : Being) : String :=
  let attrs := Attribute.all.map fun a => s!"{a.name} {b.attr a}: {attributeCost a (b.attr a)}"
  let skills := b.skills.map fun (s, l) =>
    match b.skillStep s l with
    | some _ => s!"{s.name} {l}: {b.skillCost (s, l)}"
    | none => s!"{s.name} {l}: too low to buy"
  let dr := if b.naturalDR = 0 then [] else [s!"natural DR {b.naturalDR}: {naturalDRCost b.naturalDR}"]
  s!"{", ".intercalate (attrs ++ skills ++ dr)}. Total: {b.points}"

/-! ## Tests -/

/-- A small legal Draft: a Character with a staff, two Scenes, a roll, and a Fight. -/
def fixtureLegal : String := r##"{
  "title": "The Mill Pond",
  "world": "A river valley of millers",
  "intro": "A quiet river valley, where the mill wheels turn all day. You are Wren, a miller's child who hears the river talk.",
  "character": {"name": "Wren", "background": "A miller's child who hears the river talk.",
    "st": 10, "dx": 11, "iq": 12, "ht": 12,
    "skills": [{"skill": "staff", "level": 13}, {"skill": "swimming", "level": 12},
               {"skill": "naturalist", "level": 12}, {"skill": "survival", "level": 12},
               {"skill": "firstAid", "level": 13}, {"skill": "climbing", "level": 11},
               {"skill": "fastTalk", "level": 11}],
    "weapon": "quarterstaff", "armor": "none"},
  "themeNames": {"skills": [{"skill": "staff", "name": "Stick-fighting"}],
                 "weapons": [{"weapon": "quarterstaff", "name": "Ash Pole"}], "armor": []},
  "start": 0,
  "scenes": [
    {"id": 0, "title": "The Pond", "text": "The water is black and still.",
     "choices": [
       {"text": "Swim across", "outcome": {"type": "roll", "against": "swimming", "modifier": -1, "onSuccess": 2, "onFailure": 1}},
       {"text": "Walk round", "outcome": {"type": "goto", "next": 1}}]},
    {"id": 1, "title": "The Otter", "text": "A huge otter bars the path.",
     "choices": [{"text": "Fight it", "outcome": {"type": "fight", "onWin": 2, "foes": [
       {"name": "Giant Otter", "st": 9, "dx": 11, "iq": 4, "ht": 11, "skills": [{"skill": "brawling", "level": 12}],
        "weapon": "punch", "armor": "none", "naturalDR": 0}]}}]},
    {"id": 2, "title": "Home", "text": "You reach the mill.", "choices": []}]
}"##

/-- Fixture: the same Draft, but the Character costs too much and Scene 1 loops forever. -/
def fixtureIllegal : String :=
  (fixtureLegal.replace "\"st\": 10, \"dx\": 11," "\"st\": 12, \"dx\": 11,").replace
    "{\"text\": \"Fight it\", \"outcome\": {\"type\": \"fight\", \"onWin\": 2,"
    "{\"text\": \"Fight it\", \"outcome\": {\"type\": \"fight\", \"onWin\": 1,"

/-- Fixture: the same Draft, but winning the Fight in Scene 1 goes back to Scene 0. This makes a
loop of 2 steps. -/
def fixtureShortLoop : String :=
  fixtureLegal.replace
    "{\"text\": \"Fight it\", \"outcome\": {\"type\": \"fight\", \"onWin\": 2,"
    "{\"text\": \"Fight it\", \"outcome\": {\"type\": \"fight\", \"onWin\": 0,"

/-- Fixture: the same Draft, but the text of Scene 2 is 2,001 characters long. -/
def fixtureTooLong : String :=
  fixtureLegal.replace "You reach the mill." ("".pushn 'x' 2001)

/-- Fixture: the same Draft as an older save, with no World and no Intro. -/
def fixtureOld : String :=
  (fixtureLegal.replace "  \"world\": \"A river valley of millers\",\n" "").replace
    "  \"intro\": \"A quiet river valley, where the mill wheels turn all day. You are Wren, a miller's child who hears the river talk.\",\n" ""

/-- `true` if the JSON text reads as a Draft and the Draft passes the checker. -/
def passesChecker (s : String) : Bool :=
  match Draft.parse s with
  | .ok d => (d.checked matches .ok _)
  | .error _ => false

/-- The errors for JSON text: the decoder's error, or the Draft's errors. -/
def draftErrors (s : String) : List String :=
  match Draft.parse s with
  | .ok d => d.errors
  | .error e => [e]

-- The legal fixture reads and passes the checker.
#guard passesChecker fixtureLegal
#guard draftErrors fixtureLegal == []
-- Its Theme Names are read.
#guard match Draft.parse fixtureLegal with
  | .ok d => d.adventure.themes.weapon .quarterstaff == "Ash Pole" &&
      d.adventure.themes.skill .swimming == "Swimming" &&
      d.hero.points == liveRules.characterPoints
  | .error _ => false
-- Writing a Draft as JSON and reading it back gives the same Draft.
#guard match Draft.parse fixtureLegal with
  | .ok d => (Draft.ofJson d.toJson).toOption.map (fun d' => reprStr d' == reprStr d) == some true
  | .error _ => false
-- The World and the Intro are read.
#guard match Draft.parse fixtureLegal with
  | .ok d => d.world == "A river valley of millers" && d.intro.startsWith "A quiet river valley"
  | .error _ => false
-- An older save with no World and no Intro still reads and can be played. Both are empty.
#guard !(fixtureOld.contains "\"world\"") && !(fixtureOld.contains "\"intro\"")
#guard passesChecker fixtureOld
#guard match Draft.parse fixtureOld with
  | .ok d => d.world == "" && d.intro == ""
  | .error _ => false
-- A World over 60 characters fails the size limit.
#guard draftErrors (fixtureLegal.replace "A river valley of millers" ("".pushn 'w' 61)) ==
  ["the world has 61 characters, but the limit is 60"]
-- The illegal fixture fails the checker: the Character costs 120 points, and Scene 1 has
-- no way to an Ending.
#guard !passesChecker fixtureIllegal
#guard (draftErrors fixtureIllegal).any (·.startsWith "Wren: costs 120 points")
#guard (draftErrors fixtureIllegal).any (·.startsWith "Scene 1 (The Otter) has no way to an Ending")
-- The short-loop fixture fails only the short-loop check. The error names the Scenes of the loop.
#guard !passesChecker fixtureShortLoop
#guard draftErrors fixtureShortLoop ==
  ["the loop Scene 0 -> Scene 1 -> Scene 0 has 2 steps, but a loop needs at least 4 steps: make it longer or remove it"]
-- The illegal fixture also has a loop of 1 step: winning the Fight in Scene 1 goes back to Scene 1.
#guard (draftErrors fixtureIllegal).any (·.startsWith "the loop Scene 1 -> Scene 1 has 1 step")
-- The long fixture fails the size limit, and the checker does not run.
#guard draftErrors fixtureTooLong == ["the text of Scene 2 has 2001 characters, but the limit is 2000"]
#guard !passesChecker fixtureTooLong
-- Bad JSON gives a plain error that names the place.
#guard draftErrors (fixtureLegal.replace "\"swimming\", \"modifier\"" "\"flying\", \"modifier\"") ==
  ["scenes 1: Scene 0: choices 1: outcome: \"flying\" is not a roll target. Use one of: broadsword, knife, brawling, stealth, lockpicking, diplomacy, survival, naturalist, occultism, riding, climbing, swimming, firstAid, fastTalk, staff, liquidProjector, ST, DX, IQ, HT"]
#guard (draftErrors "{\"title\": 3}").length == 1
-- The points of the legal Character add up to 100.
#guard match Draft.parse fixtureLegal with
  | .ok d => pointsBreakdown d.hero ==
      "ST 10: 0, DX 11: 20, IQ 12: 40, HT 12: 20, Staff 13: 8, Swimming 12: 1, Naturalist 12: 4, Survival 12: 2, First Aid 13: 2, Climbing 11: 2, Fast-Talk 11: 1. Total: 100"
  | .error _ => false

-- A Draft with a world map passes, saves its map, and reads it back. The map of the legal fixture
-- has a place for each of its 3 Scenes.
#guard match Draft.parse fixtureLegal with
  | .ok d =>
    let withMap := { d with environment := some testMap }
    withMap.errors == [] &&
      (Draft.ofJson withMap.toJson).toOption.map (fun saved => saved.environment == some testMap) == some true
  | .error _ => false
-- A Draft with no map has no `environment` field, so an older save keeps its text.
#guard match Draft.parse fixtureLegal with
  | .ok d => (d.toJson.getObjVal? "environment").toOption.isNone
  | .error _ => false
-- A bad map is a size error, so the checker does not run, and the error names the Scene.
#guard match Draft.parse fixtureLegal with
  | .ok d => { d with environment := some { testMap with scenes := testMap.scenes.drop 1 } }.errors ==
      ["environment: Scene 0 needs exactly one place"]
  | .error _ => false

/-- Fixture: the legal Draft, saved at difficulty level `key`. -/
def fixtureAt (key : String) : String :=
  fixtureLegal.replace "\"start\": 0," s!"\"start\": 0, \"difficulty\": \"{key}\","

-- A Draft with no `difficulty` field is medium. Each level reads back from its JSON name.
#guard (Draft.parse fixtureLegal).toOption.map (·.difficulty) == some .medium
#guard (Draft.parse fixtureOld).toOption.map (·.difficulty) == some .medium
#guard (Draft.parse (fixtureAt "easy")).toOption.map (·.difficulty) == some .easy
#guard (Draft.parse (fixtureAt "hard")).toOption.map (·.difficulty) == some .hard
-- A level that does not exist is an error, not medium.
#guard draftErrors (fixtureAt "extreme") == ["difficulty: \"extreme\" is not easy, medium, or hard"]
-- A saved level reads back the same.
#guard match Draft.parse (fixtureAt "hard") with
  | .ok d => (Draft.ofJson d.toJson).toOption.map (·.difficulty) == some .hard
  | .error _ => false
-- A Game from an admitted Draft has the policy of the Draft's level.
#guard match Draft.parse (fixtureAt "hard") with
  | .ok d => (d.toGameAdmitted.toOption.map (·.policy)) == some Probability.DifficultyLevel.hard.policy
  | .error _ => false
#guard match Draft.parse fixtureOld with
  | .ok d => (d.toGameAdmitted.toOption.map (·.policy)) == some Probability.DifficultyLevel.medium.policy
  | .error _ => false

-- The balance check uses the curve of the Draft's level. On turn 6 the allowed range is
-- 16.3% to 26.3% on medium (the default), and 31.9% to 41.9% on hard.
#guard match Draft.parse fixtureLegal with
  | .ok d => match d.toGame 1 with
    | .ok _ => false
    | .error errs => errs.any (·.endsWith "the allowed range is 16.3% to 26.3%")
  | .error _ => false
#guard match Draft.parse (fixtureAt "hard") with
  | .ok d => match d.toGame 1 with
    | .ok _ => false
    | .error errs => errs.any (·.endsWith "the allowed range is 31.9% to 41.9%") &&
      !errs.any (·.endsWith "the allowed range is 16.3% to 26.3%")
  | .error _ => false

-- The legal fixture passes the checker but fails the balance check: it is too short and too safe.
-- Every row from turn 4 on has no games in it, so those rows cannot pass.
#guard match Draft.parse fixtureLegal with
  | .ok d => match d.toGame 1 with
    | .ok _ => false
    | .error errs => errs.all (·.startsWith "balance: ") && !errs.isEmpty
  | .error _ => false

end Rpg
