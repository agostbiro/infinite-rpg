import Rpg.GraphValidity
import Rpg.Probability.TestStory

/-! Concrete positive and negative cases for the combined validity test.
The short safe example exercises horizon one; live Wishes still require horizon fourteen. -/
namespace Rpg
open Probability Probability.TestStory

/-- This concrete short-window graph has legal structure and no short event cycles. -/
example : safeCandidate.story.NoShortCycles := by decide

-- The real validator accepts this example and rejects the longer-window unsafe balance claim.
#guard (validateGraph safeCandidate 1).isOk
#guard !(validateGraph safeCandidate5 1).isOk

/-- A concrete invocation yields the validity theorem for precisely its returned certificate. -/
example : ∀ g, validateGraph safeCandidate 1 = .ok g →
    GraphValid g.statistical.candidate g.statistical.seed g.statistical.counts := by
  intro g _
  exact g.equilibrium

end Rpg
