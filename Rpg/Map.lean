import Rpg.Play

/-!
# Map

The map shows where the Character has been. The page only draws it; this file decides what is on it.

* Each visited Scene is a box. The boxes go down the map in the order of the first visit.
* A solid line joins two Scenes for each Choice the Character took.
* A Choice of a visited Scene that leads to a Scene not yet visited shows as a "?" box.
  The map does not say what kind of Choice it is.
* After a Success Roll, the branch not taken shows as a dashed line marked "on success" or
  "on failure". It leads to a "?" box, or to its Scene if the Character has been there.
* A Fight has only one branch, so it never has a dashed line.
-/

namespace Rpg

open Lean

/-- A box on the map. -/
structure MapNode where
  /-- A name for the box that is unique on this map. -/
  key : String
  /-- The Scene title, or "?" for a place not yet visited. -/
  label : String
  /-- `true` for a visited Scene, `false` for a "?" box. -/
  visited : Bool
  /-- The row, from 0 at the top. -/
  row : Nat
  /-- The column: 0 for visited Scenes, 1 and up for "?" boxes beside them. -/
  col : Nat
  /-- `true` if play is in this Scene now. -/
  current : Bool
  /-- `true` if this Scene is an Ending. -/
  ending : Bool
  /-- `true` if the Character died in this Scene. -/
  dead : Bool
  deriving ToJson, BEq, Repr

/-- A line on the map. -/
structure MapEdge where
  source : String
  target : String
  /-- "taken" for a Choice the Character took, "branch" for the Success Roll result
  that did not happen, "unknown" for a Choice not taken. -/
  style : String
  /-- "on success", "on failure", or "". -/
  label : String
  deriving ToJson, BEq, Repr

/-- The whole map. -/
structure GameMap where
  nodes : List MapNode
  edges : List MapEdge
  deriving ToJson, Repr

/-- The list with each value kept only at its first place. -/
def firstEach [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The Scenes the Character has visited, in the order of the first visit. -/
def Game.visited (g : Game) : List SceneId :=
  match g.phase with
  | .title => []
  | _ => firstEach (g.adventure.start :: g.trail.map (·.target))

/-- The map key of a visited Scene. -/
def sceneKey (id : SceneId) : String := s!"s{id}"

/-- The Fight that play is in, or where the Character died: its Scene and Choice number. -/
def Game.openFight? (g : Game) : Option (SceneId × Nat) :=
  match g.phase with
  | .fight f => some (f.scene, f.choice)
  | .dead f => some (f.scene, f.choice)
  | _ => none

/-- The map of a game. -/
def Game.map (g : Game) : GameMap := Id.run do
  let visited := g.visited
  let mut nodes : List MapNode := []
  let mut edges : List MapEdge := []
  for (id, row) in visited.zipIdx do
    let some sc := g.adventure.scene? id | continue
    nodes := nodes ++ [{
      key := sceneKey id, label := sc.title, visited := true, row, col := 0,
      current := g.sceneId? == some id, ending := sc.choices.isEmpty,
      dead := g.phase.name == "dead" && g.sceneId? == some id }]
    let mut col := 1
    for (ch, k) in sc.choices.zipIdx do
      let taken := g.trail.filter fun t => t.source == id && t.choice == k
      let targets := firstEach (taken.map (·.target))
      -- A "?" box, or a line to a Scene the Character has visited.
      let mut branches : List (SceneId × String × String) := []
      if taken.isEmpty then
        -- A Fight that is going on, or where the Character died, is not a way still open.
        if g.openFight? != some (id, k) && ch.outcome.targets.any (· ∉ visited) then
          branches := [(id, "unknown", "")]
      else
        for t in targets do
          edges := edges ++ [{ source := sceneKey id, target := sceneKey t, style := "taken", label := "" }]
        if let .roll _ _ onSuccess onFailure := ch.outcome then
          let results := taken.filterMap (·.rolled)
          if !results.contains true && onSuccess ∉ targets then
            branches := branches ++ [(onSuccess, "branch", "on success")]
          if !results.contains false && onFailure ∉ targets then
            branches := branches ++ [(onFailure, "branch", "on failure")]
      for (b, style, label) in branches do
        if style == "branch" && b ∈ visited then
          edges := edges ++ [{ source := sceneKey id, target := sceneKey b, style, label }]
        else
          let key := s!"q{id}-{k}-{col}"
          nodes := nodes ++ [{
            key, label := "?", visited := false, row, col,
            current := false, ending := false, dead := false }]
          edges := edges ++ [{ source := sceneKey id, target := key, style, label }]
          col := col + 1
  return { nodes, edges := firstEach edges }

/-! ## Tests -/

-- On the title screen, the map is empty.
#guard titleGame.map.nodes.isEmpty

-- In The Road, the map shows The Road and one "?" box per Choice.
#guard
  let m := ((step titleGame .begin).run' ⟨7⟩).1.map
  m.nodes.map (·.label) == ["The Road", "?", "?"] &&
    m.edges.map (·.style) == ["unknown", "unknown"]

-- After the roll to climb the bank succeeds, the failure branch shows as a dashed line to a "?" box.
-- The Wall Top shows its one Choice as a "?" box.
#guard
  let m := ((step roadGame (.choose 1)).run' ⟨7⟩).1.map
  m.nodes.map (·.label) == ["The Road", "?", "?", "The Wall Top", "?"] &&
    m.edges == [
      { source := "s0", target := "q0-0-1", style := "unknown", label := "" },
      { source := "s0", target := "s2", style := "taken", label := "" },
      { source := "s0", target := "q0-1-2", style := "branch", label := "on failure" },
      { source := "s2", target := "q2-0-1", style := "unknown", label := "" }]

/-- Play a list of inputs from the title screen with seed 7. -/
def playSeed7 (inputs : List Input) : Game :=
  (inputs.foldl (fun (g, dice) i => let ((g, _), dice) := (step g i).run dice; (g, dice))
    (titleGame, ⟨7⟩)).1

-- Walk up to the gate, hammer on it, and start the Fight with the bandits.
-- The Fight Choice shows no "?" box, and a Fight has no dashed line.
#guard
  let g := playSeed7 [.begin, .choose 0, .choose 1, .choose 0]
  let m := g.map
  g.phase.name == "fight" &&
    m.nodes.map (·.label) == ["The Road", "?", "The Gate", "?", "?", "Bandits!"] &&
    m.edges.all (·.style != "branch")

end Rpg
