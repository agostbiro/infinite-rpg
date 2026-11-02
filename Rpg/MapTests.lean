import Rpg.Map
import Rpg.PlayTests

namespace Rpg


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
