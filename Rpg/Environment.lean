import Rpg.Adventure
import Lean

/-! A bounded scene plan for the renderer. It contains no game commands or outcomes.
These runtime checks validate the file structure, not the physics or renderer. -/
namespace Rpg
open Lean

/-- One named place, in metres on the common horizontal map. -/
structure WorldPlace where
  id : Nat
  name : String
  kind : String
  x : Int
  z : Int
  deriving Repr, ToJson, FromJson

/-- A visible trail between two places. It never advances the adventure graph. -/
structure WorldPath where
  fromPlace : Nat
  toPlace : Nat
  deriving Repr, ToJson, FromJson

/-- A decorative model from a finite local asset vocabulary. Scale is a percentage. -/
structure WorldProp where
  kind : String
  x : Int
  z : Int
  scale : Nat := 100
  heading : Nat := 0
  deriving Repr, ToJson, FromJson

/-- The place hosting the options of one logical scene. -/
structure ScenePlace where
  scene : Nat
  place : Nat
  npcs : List String := []
  deriving Repr, ToJson, FromJson

/-- The generated environment shared by the whole adventure. -/
structure WorldEnvironment where
  theme : String
  places : List WorldPlace
  paths : List WorldPath
  props : List WorldProp
  scenes : List ScenePlace
  deriving Repr, ToJson, FromJson

/-- Renderer themes accepted in generated files. -/
def worldThemes : List String := ["desert", "forest", "coast", "snow", "space", "city"]

/-- Place models supported by the renderer. -/
def worldPlaceKinds : List String := ["camp", "harbour", "village", "market", "ruins", "temple", "forest", "outpost"]

/-- Decorative models supported by the renderer. -/
def worldPropKinds : List String := ["pyramid", "palm", "tree", "rock", "house", "tent", "column", "boat", "river"]

/-- A conservative horizontal radius for obstacle placement. -/
def WorldProp.radius (p : WorldProp) : Int :=
  let base := if p.kind == "pyramid" then 12 else if p.kind == "house" then 5
    else if p.kind == "river" then 0 else 3
  (base * p.scale + 99) / 100

/-- Places reachable by the undirected visible trails, with duplicates removed. -/
def WorldEnvironment.connected (e : WorldEnvironment) : List Nat :=
  let rec go : Nat → List Nat → List Nat
    | 0, seen => seen
    | fuel + 1, seen =>
      let found := e.paths.flatMap fun p =>
        (if seen.contains p.fromPlace then [p.toPlace] else []) ++
        (if seen.contains p.toPlace then [p.fromPlace] else [])
      go fuel (seen ++ found).eraseDups
  go e.places.length (e.places.head?.map (fun p => [p.id]) |>.getD [])

/-- Validate sizes, supported models, coordinates, connectivity and exact scene coverage. -/
def WorldProp.blocksPath (p : WorldProp) (a b : WorldPlace) : Bool :=
  let dx := b.x-a.x
  let dz := b.z-a.z
  let ux := p.x-a.x
  let uz := p.z-a.z
  let len := dx^2 + dz^2
  let dot := ux*dx + uz*dz
  let radius := p.radius + 2
  if dot ≤ 0 then ux^2 + uz^2 < radius^2
  else if dot ≥ len then (p.x-b.x)^2 + (p.z-b.z)^2 < radius^2
  else (ux*dz-uz*dx)^2 < radius^2 * len

/-- Structural checks also keep a walkable corridor along each declared path. -/
def WorldEnvironment.errors (e : WorldEnvironment) (a : Adventure) : List String := Id.run do
  let mut errors := []
  if !worldThemes.contains e.theme then errors := errors ++ ["environment: unsupported theme"]
  if e.places.length < 2 || e.places.length > 12 then
    errors := errors ++ ["environment: provide 2 to 12 places"]
  if e.paths.length > 30 || e.props.length > 80 || e.scenes.length > 128 then
    errors := errors ++ ["environment: too many paths, props or scene mappings"]
  let ids := e.places.map (·.id)
  if ids.eraseDups.length != ids.length then errors := errors ++ ["environment: duplicate place id"]
  for p in e.places do
    if p.name.isEmpty || p.name.length > 60 || !worldPlaceKinds.contains p.kind then
      errors := errors ++ [s!"environment: invalid place {p.id}"]
    if p.x < -85 || p.x > 85 || p.z < -85 || p.z > 85 then
      errors := errors ++ [s!"environment: place {p.id} is outside the map"]
    if e.places.any (fun q => q.id != p.id && (q.x-p.x)^2 + (q.z-p.z)^2 < 24^2) then
      errors := errors ++ [s!"environment: place {p.id} is too close to another place (minimum 24 metres)"]
  for p in e.paths do
    if !ids.contains p.fromPlace || !ids.contains p.toPlace || p.fromPlace == p.toPlace then
      errors := errors ++ ["environment: a path has invalid endpoints"]
  if ids.any (fun id => !e.connected.contains id) then errors := errors ++ ["environment: connect every place with paths"]
  for p in e.props do
    if !worldPropKinds.contains p.kind || p.scale < 50 || p.scale > 200 || p.heading > 359 then
      errors := errors ++ ["environment: invalid prop kind, scale or heading"]
    if p.x < -100 || p.x > 100 || p.z < -100 || p.z > 100 then
      errors := errors ++ ["environment: prop outside the map"]
    if p.kind != "river" && e.places.any (fun q => (q.x-p.x)^2 + (q.z-p.z)^2 < (p.radius+10)^2) then
      errors := errors ++ ["environment: keep props clear of each place's 10-metre interaction area"]
    if p.kind != "river" then
      for path in e.paths do
        match e.places.find? (·.id == path.fromPlace), e.places.find? (·.id == path.toPlace) with
        | some a, some b =>
          if p.blocksPath a b then errors := errors ++ ["environment: a solid prop blocks a path corridor"]
        | _, _ => pure ()
  for s in a.scenes do
    if s.choices.length > 4 then
      errors := errors ++ [s!"environment: Scene {s.id} has more than 4 spatial choices"]
    if (e.scenes.filter (·.scene == s.id)).length != 1 then
      errors := errors ++ [s!"environment: Scene {s.id} needs exactly one place mapping"]
  for s in e.scenes do
    if !(a.scenes.any (·.id == s.scene)) || !ids.contains s.place then
      errors := errors ++ [s!"environment: unknown scene or place in mapping {s.scene}"]
    if s.npcs.length > 4 || s.npcs.any (fun n => n.isEmpty || n.length > 60) then
      errors := errors ++ [s!"environment: Scene {s.scene} needs at most 4 NPC names, each 1 to 60 characters"]
  return errors

end Rpg
