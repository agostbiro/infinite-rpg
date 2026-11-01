import Rpg.EventGraph
import Lean

/-!
# World maps

A world map tells the 3D page where each Scene of an Adventure takes place: up to 12 named places,
the paths between them, some props (trees, houses, rivers), and one place for each Scene. The DM
writes it with the Adventure. It changes only what the Player sees, never what the rules do: it has
no Choices, no dice, and no outcomes.

`WorldEnvironment.errors` is a run-time check of the file. It checks the sizes, the kinds of things
the page can draw, the coordinates, that every place can be reached on the paths, that no solid prop
blocks a path, and that each Scene has exactly one place. It has no proofs, and none are needed:
the page uses the map only for what the Player sees, and the server checks the story without it.

The map format and its check come from code by antoine-vinciguerra (branch `RPG_3D`).
-/

namespace Rpg
open Lean

/-- One named place. `x` and `z` are in metres on the flat map. -/
structure WorldPlace where
  id : Nat
  name : String
  kind : String
  x : Int
  z : Int
  deriving Repr, BEq, ToJson, FromJson

/-- A path that the Player can see between two places. Walking on it never picks a Choice. -/
structure WorldPath where
  fromPlace : Nat
  toPlace : Nat
  deriving Repr, BEq, ToJson, FromJson

/-- A prop from the fixed list of models that the page can draw. `scale` is a percentage, and
`heading` is in degrees. -/
structure WorldProp where
  kind : String
  x : Int
  z : Int
  scale : Nat := 100
  heading : Nat := 0
  deriving Repr, BEq, ToJson, FromJson

/-- The place of one Scene, and the names of the people that the page shows there. -/
structure ScenePlace where
  scene : Nat
  place : Nat
  npcs : List String := []
  deriving Repr, BEq, ToJson, FromJson

/-- The world map of an Adventure. -/
structure WorldEnvironment where
  theme : String
  places : List WorldPlace
  paths : List WorldPath
  props : List WorldProp
  scenes : List ScenePlace
  deriving Repr, BEq, ToJson, FromJson

/-- The themes that the page can draw. -/
def worldThemes : List String := ["desert", "forest", "coast", "snow", "space", "city"]

/-- The kinds of place that the page can draw. -/
def worldPlaceKinds : List String :=
  ["camp", "harbour", "village", "market", "ruins", "temple", "forest", "outpost"]

/-- The kinds of prop that the page can draw. -/
def worldPropKinds : List String :=
  ["pyramid", "palm", "tree", "rock", "house", "tent", "column", "boat", "river"]

/-- The most places on a map. -/
def maxWorldPlaces : Nat := 12

/-- A safe radius of a prop on the ground, in metres. A river has none: the Player can wade it. -/
def WorldProp.radius (p : WorldProp) : Int :=
  let base := if p.kind == "pyramid" then 12 else if p.kind == "house" then 5
    else if p.kind == "river" then 0 else 3
  (base * p.scale + 99) / 100

/-- The places that the paths connect to the first place, with each place once. -/
def WorldEnvironment.connected (e : WorldEnvironment) : List Nat :=
  let rec go : Nat → List Nat → List Nat
    | 0, seen => seen
    | fuel + 1, seen =>
      let found := e.paths.flatMap fun p =>
        (if seen.contains p.fromPlace then [p.toPlace] else []) ++
        (if seen.contains p.toPlace then [p.fromPlace] else [])
      go fuel (seen ++ found).eraseDups
  go e.places.length (e.places.head?.map (fun p => [p.id]) |>.getD [])

/-- `true` if prop `p` is closer than its radius plus 2 metres to the path from `a` to `b`. Then
it blocks the 4-metre lane along the path. -/
def WorldProp.blocksPath (p : WorldProp) (a b : WorldPlace) : Bool :=
  let dx := b.x - a.x
  let dz := b.z - a.z
  let ux := p.x - a.x
  let uz := p.z - a.z
  let len := dx ^ 2 + dz ^ 2
  let dot := ux * dx + uz * dz
  let radius := p.radius + 2
  if dot ≤ 0 then ux ^ 2 + uz ^ 2 < radius ^ 2
  else if dot ≥ len then (p.x - b.x) ^ 2 + (p.z - b.z) ^ 2 < radius ^ 2
  else (ux * dz - uz * dx) ^ 2 < radius ^ 2 * len

/-- The errors of a world map for the Adventure `a`, in words for the DM. An empty list means the
page can draw the map, and each Scene has one place. -/
def WorldEnvironment.errors (e : WorldEnvironment) (a : Adventure) : List String := Id.run do
  let mut errors := []
  if !worldThemes.contains e.theme then
    errors := errors ++ [s!"environment: the theme must be one of {", ".intercalate worldThemes}"]
  if e.places.length < 2 || e.places.length > maxWorldPlaces then
    errors := errors ++ [s!"environment: give 2 to {maxWorldPlaces} places"]
  if e.paths.length > 30 || e.props.length > 80 || e.scenes.length > 128 then
    errors := errors ++ ["environment: give at most 30 paths, 80 props, and 128 Scene places"]
  let ids := e.places.map (·.id)
  if ids.eraseDups.length != ids.length then
    errors := errors ++ ["environment: two places have the same id"]
  for p in e.places do
    if p.name.isEmpty || p.name.length > 60 || !worldPlaceKinds.contains p.kind then
      errors := errors ++ [s!"environment: place {p.id} needs a name of 1 to 60 characters and a kind from {", ".intercalate worldPlaceKinds}"]
    if p.x < -85 || p.x > 85 || p.z < -85 || p.z > 85 then
      errors := errors ++ [s!"environment: place {p.id} is outside the map (x and z from -85 to 85)"]
    if e.places.any (fun q => q.id != p.id && (q.x - p.x) ^ 2 + (q.z - p.z) ^ 2 < 24 ^ 2) then
      errors := errors ++ [s!"environment: place {p.id} is less than 24 metres from another place"]
  for p in e.paths do
    if !ids.contains p.fromPlace || !ids.contains p.toPlace || p.fromPlace == p.toPlace then
      errors := errors ++ [s!"environment: the path from {p.fromPlace} to {p.toPlace} must join two different places"]
  if ids.any (fun id => !e.connected.contains id) then
    errors := errors ++ ["environment: the paths must connect every place"]
  for p in e.props do
    if !worldPropKinds.contains p.kind || p.scale < 50 || p.scale > 200 || p.heading > 359 then
      errors := errors ++ [s!"environment: a prop needs a kind from {", ".intercalate worldPropKinds}, a scale of 50 to 200, and a heading of 0 to 359"]
    if p.x < -100 || p.x > 100 || p.z < -100 || p.z > 100 then
      errors := errors ++ ["environment: a prop is outside the map (x and z from -100 to 100)"]
    if p.kind != "river" && e.places.any (fun q => (q.x - p.x) ^ 2 + (q.z - p.z) ^ 2 < (p.radius + 10) ^ 2) then
      errors := errors ++ [s!"environment: the {p.kind} at ({p.x}, {p.z}) is too close to a place. Keep 10 metres plus its radius clear"]
    if p.kind != "river" then
      for path in e.paths do
        match e.places.find? (·.id == path.fromPlace), e.places.find? (·.id == path.toPlace) with
        | some a, some b =>
          if p.blocksPath a b then
            errors := errors ++ [s!"environment: the {p.kind} at ({p.x}, {p.z}) blocks the path from {a.id} to {b.id}"]
        | _, _ => pure ()
  -- A long story must use the whole map.
  if a.scenes.length >= 16 then
    for p in e.places do
      if !e.scenes.any (·.place == p.id) then
        errors := errors ++ [s!"environment: no Scene takes place at {p.name}"]
    -- Each pair `(s, t)` where a Choice in Scene `s` can lead to Scene `t`, with each pair once.
    let edges := a.links.eraseDups
    let placeOf (s : SceneId) := (e.scenes.find? (·.scene == s)).map (·.place)
    let cross := edges.filter fun (u, v) => placeOf u != placeOf v
    if cross.length * 3 < edges.length then
      errors := errors ++ ["environment: at least one third of the Choices must lead to another place"]
  for s in a.scenes do
    if s.choices.length > 4 then
      errors := errors ++ [s!"environment: Scene {s.id} has more than 4 Choices, so the 3D world cannot show them well"]
    if (e.scenes.filter (·.scene == s.id)).length != 1 then
      errors := errors ++ [s!"environment: Scene {s.id} needs exactly one place"]
  for s in e.scenes do
    if !(a.scenes.any (·.id == s.scene)) || !ids.contains s.place then
      errors := errors ++ [s!"environment: the place of Scene {s.scene} names a Scene or a place that does not exist"]
    if s.npcs.length > 4 || s.npcs.any (fun n => n.isEmpty || n.length > 60) then
      errors := errors ++ [s!"environment: Scene {s.scene} can name at most 4 people, each with 1 to 60 characters"]
  return errors

/-! ## Tests -/

/-- A small story for the tests: Scene 0 leads to Scene 1 or Scene 2, and both are Endings. -/
private def testStory : Adventure :=
  { title := "Map test", start := 0, scenes := [
      { id := 0, title := "Camp", text := "", choices := [
          { text := "Walk to the woods", outcome := .goto 1 }, { text := "Stay", outcome := .goto 2 }] },
      { id := 1, title := "Woods", text := "", choices := [] },
      { id := 2, title := "Home", text := "", choices := [] }] }

/-- A small map for the tests: two places, one path, one tree, and a place for each Scene. -/
def testMap : WorldEnvironment := {
  theme := "forest"
  places := [{ id := 0, name := "Camp", kind := "camp", x := 0, z := 0 },
    { id := 1, name := "Forest", kind := "forest", x := 40, z := 0 }]
  paths := [{ fromPlace := 0, toPlace := 1 }]
  props := [{ kind := "tree", x := 20, z := 20 }]
  scenes := [{ scene := 0, place := 0 }, { scene := 1, place := 1 }, { scene := 2, place := 0 }] }

-- The test map passes.
#guard testMap.errors testStory == []
-- A map with no path, a Scene with no place, a place that is not on the map, two places with the
-- same id, a tree on the path, a prop the page cannot draw, or a prop outside the map fails.
#guard [{ testMap with paths := [] },
    { testMap with scenes := testMap.scenes.drop 1 },
    { testMap with scenes := { scene := 2, place := 7 } :: testMap.scenes.drop 1 },
    { testMap with places := testMap.places ++ testMap.places },
    { testMap with props := [{ kind := "tree", x := 20, z := 0 }] },
    { testMap with props := [{ kind := "dragon", x := 20, z := 20 }] },
    { testMap with props := [{ kind := "tree", x := 101, z := 20 }] }].all
  fun e => !(e.errors testStory).isEmpty
-- The error names the Scene that has no place.
#guard (({ testMap with scenes := testMap.scenes.drop 1 }).errors testStory) ==
  ["environment: Scene 0 needs exactly one place"]
-- A map reads back from its JSON.
#guard (fromJson? (toJson testMap) : Except String WorldEnvironment).toOption == some testMap

end Rpg
