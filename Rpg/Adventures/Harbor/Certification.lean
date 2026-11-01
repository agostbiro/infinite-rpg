import Rpg.Adventures.Harbor.Story
import Rpg.Probability.Fairness
namespace Rpg.Harbor
open Probability
/-- The tutorial graph is derived from the same story played by the engine. -/
def harborGraph := adventureGraph rules iona harbor
/-- A deterministic transition has total probability one. -/
theorem harbor_pure_valid (x : Node) : (pure x : Distribution Node).Valid := by
  simp [Distribution.Valid, pure, Pure.pure]
  decide +kernel
/-- Every scene transition in the tutorial is a valid distribution. -/
theorem harbor_scene_valid (id : Nat) (hp : Int) : (harborGraph.step (.scene id hp)).Valid := by
  by_cases h0 : id = 0
  · subst id
    by_cases hp0 : hp ≤ 0
    · simp [harborGraph, adventureGraph, harbor, Adventure.scene?, outcomeEdges, arrive, hp0,
        uniform, Distribution.bind, Distribution.collect, Distribution.Valid, pure, Pure.pure]
      all_goals decide +kernel
    · simp [harborGraph, adventureGraph, harbor, Adventure.scene?, outcomeEdges, arrive, hp0,
        uniform, Distribution.bind, Distribution.collect, Distribution.Valid, pure, Pure.pure]
      all_goals decide +kernel
  · by_cases h1 : id = 1
    · subst id
      simp [harborGraph, adventureGraph, harbor, Adventure.scene?, Distribution.Valid, pure, Pure.pure]
      all_goals decide +kernel
    · have b0 : (0 == id) = false := by simp [Ne.symm h0]
      have b1 : (1 == id) = false := by simp [Ne.symm h1]
      simp [harborGraph, adventureGraph, harbor, Adventure.scene?, List.find?, b0, b1, Distribution.Valid, pure, Pure.pure]
      all_goals decide +kernel

/-- The tutorial graph has normalized transitions and absorbing terminal states. -/
theorem harbor_graph_valid : harborGraph.Valid := by
  constructor
  · intro node
    cases node with
    | scene id hp => exact harbor_scene_valid id hp
    | ended => exact harbor_pure_valid .ended
    | dead => exact harbor_pure_valid .dead
    | stalled => exact harbor_pure_valid .stalled
  · exact ⟨rfl, rfl, rfl⟩

/-- The tutorial has ended after one or more scene choices. -/
theorem harbor_after (n : Nat) : harborGraph.after (n + 1) = pure Node.ended := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [Graph.after, ih]
    decide +kernel

/-- The tutorial satisfies the default two-turn fairness bound at every active time. -/
theorem harbor_isFair : isFair defaultPolicy harborGraph := by
  refine ⟨defaultPolicy_valid, harbor_graph_valid, by decide +kernel, by decide +kernel, ?_⟩
  intro t actual observed
  cases t with
  | zero =>
    have h : harborGraph.deathAtTwo 0 = some 0 := by decide +kernel
    rw [h] at observed
    cases observed
    decide +kernel
  | succ n =>
    have inactive : harborGraph.activeAt (n + 1) = 0 := by
      rw [Graph.activeAt, harbor_after]
      decide +kernel
    simp [Graph.deathAtTwo, inactive] at observed

/-- Only this proof-carrying value is exposed to the playable catalog. -/
def harborCertified : CertifiedAdventure where
  rules := rules
  hero := iona
  heroLegal := iona_legal
  story := harbor
  legal := harbor_legal
  fair := harbor_isFair

end Rpg.Harbor
