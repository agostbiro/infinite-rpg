import Rpg.Live
import Rpg.Probability.TestStory

/-!
# Examples for the Draft theorems

The Comparator theorem `draft_game_policy` has premises of the form `d.toGameAdmitted = .ok g`.
This file shows a small Draft that meets that premise. Stochastic fight admission is exercised
separately in `AdmissionTests`, so this kernel example does not solve a large fight.
-/

namespace Rpg

/-- The safe test story and Mara as a Draft, as a Wish reply could give them. -/
def testDraft : Draft :=
  { adventure := Probability.TestStory.safeStory, hero := TestAdventure.mara, background := "" }

/-- The test Draft passes the size limits, legality, short-loop, and combat certificate checks. -/
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
