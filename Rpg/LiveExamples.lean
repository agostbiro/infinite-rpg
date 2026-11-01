import Rpg.Live
import Rpg.Adventures.TestAdventure

/-!
# Examples for the Draft theorems

The Comparator theorem `draft_game_policy` has premises of the form `d.toGameAdmitted = .ok g`.
This file shows a Draft that meets that premise: the test Adventure with its Character.
-/

namespace Rpg

/-- The test Adventure and Mara as a Draft, as a Wish reply could give them. -/
def testDraft : Draft :=
  { adventure := TestAdventure.testAdventure, hero := TestAdventure.mara, background := "" }

/-- The test Draft passes the size limits, the checker, and the short-loop check. -/
theorem testDraft_admitted_ok : testDraft.toGameAdmitted.isOk = true := by
  decide +kernel

/-- The premise of the fast-load half of `draft_game_policy` can be met, and then the Game has the
default curve. -/
example : ∃ g, testDraft.toGameAdmitted = .ok g ∧ g.policy = Probability.defaultPolicy := by
  have h := testDraft_admitted_ok
  cases hg : testDraft.toGameAdmitted with
  | error e =>
    rw [hg] at h
    simp [Except.isOk, Except.toBool] at h
  | ok g =>
    exact ⟨g, rfl, Draft.toGameAdmitted_policy hg⟩

end Rpg
