import Rpg.Adventures.TestAdventure.Characters

/-!
# The Bandit Camp, a test Adventure

A small Adventure for the tests. The server never offers it for play. The Comparator example
theorems are about the built-in Adventure (`Rpg/Adventures/Lafayette/`).
The theorem `test_adventure_legal` at the end proves that it is legal for Mara. If a change breaks
a rule, the build fails. Its Scenes, rolls, and Fights are the graph of the earlier built-in
Adventure, so it passes the balance check.
-/

namespace Rpg.TestAdventure

/-- The Bandit Camp. -/
def testAdventure : Adventure where
  title := "The Bandit Camp"
  start := 0
  scenes := [
    { id := 0, title := "The Road"
      text := "Rain falls on the road. Smoke rises from a bandit camp behind a wooden wall. A farmer says that the bandits hold her brother there. A gate faces the road. A steep bank climbs to the top of the wall."
      choices := [
        { text := "Walk up to the gate", outcome := .goto 1 },
        { text := "Climb the bank (DX -2)", outcome := .roll (.attribute .dx) (-2) 2 1 } ] },
    { id := 1, title := "The Gate"
      text := "The gate is barred. Behind it, you hear men laugh and dice rattle."
      choices := [
        { text := "Lift the bar through a gap (Lockpicking)", outcome := .roll (.skill .lockpicking) 0 3 4 },
        { text := "Hammer on the gate", outcome := .goto 4 },
        { text := "Say that you are a new recruit (Diplomacy -2)", outcome := .roll (.skill .diplomacy) (-2) 3 4 } ] },
    { id := 2, title := "The Wall Top"
      text := "You pull yourself onto the wall. A ladder goes down to the tent of the chief."
      choices := [
        { text := "Climb down the ladder", outcome := .goto 5 } ] },
    { id := 3, title := "The Store Tent"
      text := "The bar slides free. In the store tent, two bandits play dice by a lamp. Their backs are to you."
      choices := [
        { text := "Creep past them (Stealth -2)", outcome := .roll (.skill .stealth) (-2) 5 4 },
        { text := "Attack while they play", outcome := .goto 4 },
        { text := "Drop a cargo net on them (DX -2)", outcome := .roll (.attribute .dx) (-2) 9 4 } ] },
    { id := 4, title := "Bandits!"
      text := "Two bandits come at you with long knives."
      choices := [
        { text := "Fight", outcome := .fight [bandit 1, bandit 2] 5 } ] },
    { id := 5, title := "The Chief's Tent"
      text := "The farmer's brother sits tied to a post. The bandit chief stands over him with his sword. \"Walk away,\" he says."
      choices := [
        { text := "Talk him down (Diplomacy -3)", outcome := .roll (.skill .diplomacy) (-3) 7 6 },
        { text := "Draw your sword", outcome := .goto 6 },
        { text := "Cut the ropes with a thrown knife (DX -3)", outcome := .roll (.attribute .dx) (-3) 10 6 } ] },
    { id := 6, title := "Steel in the Tent"
      text := "The chief laughs and comes at you."
      choices := [
        { text := "Fight the bandit chief", outcome := .fight [chief] 8 } ] },
    { id := 7, title := "Ending: A Deal on the Road"
      text := "The chief thinks about your words, and your sword. He lowers his blade and walks out into the rain. You free the brother and take him home."
      choices := [] },
    { id := 8, title := "Ending: The Chief Falls"
      text := "The chief falls. You cut the brother free, and the two of you walk back down the road to the farm."
      choices := [] },
    { id := 9, title := "Caught in the Net"
      text := "The cargo net falls on one bandit. The other bandit runs at you through the ropes. You can fight them one at a time."
      choices := [
        { text := "Defeat the free bandit and go on", outcome := .fight [bandit 2] 5 } ] },
    { id := 10, title := "The Brother's Chance"
      text := "The brother pulls free and hits the chief's sword arm. The sword falls to the floor. The chief pulls a knife."
      choices := [
        { text := "Fight the chief before he finds his sword", outcome := .fight [disarmedChief] 11 },
        { text := "Tell him that the guards are on the way (IQ -2)", outcome := .roll (.attribute .iq) (-2) 7 6 } ] },
    { id := 11, title := "Ending: Two Against One"
      text := "Together you hold the chief down and tie him with his own rope. At dawn, you take him to the town guards."
      choices := [] } ]

/-- **The Bandit Camp is legal for Mara.** The Lean kernel runs the checker to prove it. -/
theorem test_adventure_legal : LegalAdventure rules mara testAdventure :=
  check_sound (by decide)

/-- Rule 7 holds for a real Adventure: from every Scene of The Bandit Camp, an Ending can be
reached. -/
theorem test_adventure_reaches_ending :
    ∀ s ∈ testAdventure.scenes, ReachesEnding testAdventure s.id :=
  test_adventure_legal.reachesEnding

/-- Rule 7 by hand, for one Scene: from Steel in the Tent (Scene 6), the Fight with the chief leads
to the Ending The Chief Falls (Scene 8). -/
example : ReachesEnding testAdventure 6 := by
  apply ReachesEnding.next (t := 8)
  -- The one Choice of Scene 6 is the Fight with the chief. A win leads to Scene 8.
  · refine ⟨testAdventure.scenes[6], by simp [testAdventure], rfl, _, List.mem_cons_self, ?_⟩
    simp [Outcome.targets]
  -- Scene 8 has no Choices, so it is an Ending.
  · exact .ending ⟨testAdventure.scenes[8], by simp [testAdventure], rfl, rfl⟩

end Rpg.TestAdventure
