import Rpg.Play
import Rpg.EventGraph

/-! The logical graph consumed by the 3D renderer is rebuilt from the current game.
Coordinates and meshes are cosmetic; commands are checked by the game engine. -/
namespace Rpg
open Lean

/-- The renderer's current logical graph and commands, independent of scene geometry. -/
structure SpatialProjection where
  scenes : List SceneId
  links : List (SceneId × SceneId)
  inputs : List Input
  deriving ToJson

/-- Build the render contract directly from this revision of the event graph. -/
def Game.spatialProjection (g : Game) : SpatialProjection :=
  ⟨g.adventure.scenes.map (·.id), g.adventure.links, g.inputs⟩

/-- Every render link is a real event transition, and every event transition is represented. -/
theorem Game.spatial_links_exact (g : Game) (source target : SceneId) :
    (source, target) ∈ g.spatialProjection.links ↔ Leads g.adventure source target := by
  constructor
  · intro h
    simp only [spatialProjection, Adventure.links, List.mem_flatMap, List.mem_map] at h
    obtain ⟨sc, hsc, ch, hch, t, ht, eq⟩ := h
    cases eq
    exact ⟨sc, hsc, rfl, ch, hch, ht⟩
  · exact Adventure.mem_links_of_leads

/-- The renderer offers every permitted command and no forbidden command. -/
theorem Game.spatial_inputs_exact (g : Game) (input : Input) :
    input ∈ g.spatialProjection.inputs ↔ AllowedInput g input := mem_inputs_iff

end Rpg
