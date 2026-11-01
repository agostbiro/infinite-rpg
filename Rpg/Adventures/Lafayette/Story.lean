import Rpg.Adventures.Lafayette.Characters
import Rpg.EventGraph

/-!
# Lafayette at Barren Hill, the built-in Adventure

The built-in Adventure. The server offers it on the Front Page, and it plays without an API key.
It is set in Pennsylvania in May 1778, during the American War of Independence. The real
Lafayette led about 2,200 men to Barren Hill, a British force tried to trap him there, and he got
away across the Schuylkill River at Matson's Ford. The people and events in the Scenes below are
invented, except for that outline.

Two choices change a later Fight. If the militia watch the Whitemarsh road (Scene 2), only one
grenadier gets to the church (Scene 4), not two (Scene 6). If Lafayette scouts the ford with Jem
(Scene 8), he meets one Loyalist scout, not two jägers in an ambush (Scene 9).

The theorem `barren_hill_legal` at the end proves that the Adventure is legal for Lafayette. If a
change breaks a rule, the build fails.
-/

namespace Rpg.Lafayette

/-- Lafayette at Barren Hill. -/
def barrenHill : Adventure where
  title := "Lafayette at Barren Hill"
  start := 0
  themes := {
    skills := [(.broadsword, "Sword"), (.knife, "Bayonet"), (.staff, "Clubbed Musket")]
    weapons := [(.broadsword, "sword"), (.largeKnife, "bayonet"), (.quarterstaff, "clubbed musket")]
    armor := [(.leather, "riding coat"), (.none, "wool coat")] }
  scenes := [
    { id := 0, title := "Valley Forge"
      text := "May 1778. The army has lived through a hard winter at Valley Forge. General Washington gives you 2,200 men and one task: watch the British in Philadelphia, and do not get caught. You are twenty years old, and some older officers think that you are too young for this. The road east passes the camp of the Pennsylvania militia."
      choices := [
        { text := "Stop at the militia camp on the way", outcome := .goto 1 },
        { text := "March straight to Barren Hill", outcome := .goto 3 } ] },
    { id := 1, title := "The Militia Camp"
      text := "Captain Hollis of the militia sits by a cook fire. His men are farmers, and they do not trust a French noble. If they watch the Whitemarsh road, no enemy can come at Barren Hill from the north without a warning."
      choices := [
        { text := "Ask him, as one soldier to another (Diplomacy -1)", outcome := .roll (.skill .diplomacy) (-1) 2 3 },
        { text := "Tell him that General Washington asks it of him (Fast-Talk)", outcome := .roll (.skill .fastTalk) 0 2 3 },
        { text := "Leave them and march on", outcome := .goto 3 } ] },
    { id := 2, title := "Barren Hill: The Road Is Watched"
      text := "You camp by the stone church on Barren Hill. Hollis's men hide in the woods along the Whitemarsh road. Your Oneida allies watch the woods to the west. At dawn, a militia boy runs in: red coats on the road!"
      choices := [
        { text := "Form the men by the church", outcome := .goto 4 },
        { text := "Ride to the ridge to see for yourself (Riding -2)", outcome := .roll (.skill .riding) (-2) 5 4 } ] },
    { id := 3, title := "Barren Hill: The Road Is Open"
      text := "You camp by the stone church on Barren Hill. No one watches the Whitemarsh road. At dawn the mist lifts, and you hear drums close by in the north."
      choices := [
        { text := "Draw your sword and rally the men", outcome := .goto 6 },
        { text := "Ride to the ridge to see the whole field (Riding -2)", outcome := .roll (.skill .riding) (-2) 5 6 } ] },
    { id := 4, title := "The Militia's Volley"
      text := "Hollis's men fire from the trees and stop the head of the British column. Only one grenadier gets to the churchyard. He lowers his bayonet at you."
      choices := [
        { text := "Fight the grenadier", outcome := .fight [grenadier 1] 7 } ] },
    { id := 5, title := "From the Ridge"
      text := "From the ridge you see the trap. British columns close on Barren Hill from the east, the north, and the south. Only the road west to Matson's Ford is still open. A dragoon scout sees you and spurs his horse."
      choices := [
        { text := "Meet the dragoon with your sword", outcome := .fight [dragoonScout] 7 },
        { text := "Gallop back to your men before he cuts you off (Riding)", outcome := .roll (.skill .riding) 0 7 6 } ] },
    { id := 6, title := "Red Coats in the Churchyard"
      text := "Two British grenadiers climb over the churchyard wall. Your men are still in their tents. The grenadiers run at the officer on the white horse."
      choices := [
        { text := "Fight the grenadiers", outcome := .fight [grenadier 1, grenadier 2] 7 } ] },
    { id := 7, title := "The Road to Matson's Ford"
      text := "You must get 2,200 men across the Schuylkill River before the trap closes. The road runs down through the woods to Matson's Ford. Jem, a miller's son from the valley, says that he knows every path to the river."
      choices := [
        { text := "Go ahead with Jem to scout the ford (Survival)", outcome := .roll (.skill .survival) 0 8 9 },
        { text := "Show small columns at the edge of the woods, so the British stop to wait for a battle (IQ -1)", outcome := .roll (.attribute .iq) (-1) 8 9 },
        { text := "March the men straight down to the ford", outcome := .goto 9 } ] },
    { id := 8, title := "The Cattle Path"
      text := "Jem sees green coats at the ford: Hessian jägers lie in the reeds and wait. He leads you down a cattle path to a shallow place up the river. Only one Loyalist scout watches it."
      choices := [
        { text := "Rush the scout", outcome := .fight [loyalistScout] 10 },
        { text := "Creep up behind him (Stealth -1)", outcome := .roll (.skill .stealth) (-1) 10 9 } ] },
    { id := 9, title := "Ambush at Matson's Ford"
      text := "Rifles crack from the reeds. Two Hessian jägers run out of the smoke with their hunting swords."
      choices := [
        { text := "Fight the jägers", outcome := .fight [jager 1, jager 2] 10 } ] },
    { id := 10, title := "Across the Schuylkill"
      text := "Your men wade the river in long lines, with the water up to their waists. The rear guard is still on the east bank. A British dragoon rides at it. The Oneida warriors wait in the trees by the water."
      choices := [
        { text := "Ride back and hold the bank with the rear guard", outcome := .fight [dragoon] 11 },
        { text := "Ask the Oneida warriors to cover the crossing (Diplomacy)", outcome := .roll (.skill .diplomacy) 0 12 13 } ] },
    { id := 11, title := "Ending: The Rear Guard Holds"
      text := "The dragoon falls back. You cross the river last of all, with the rear guard around you. On the west bank you count your men: almost all of them are there. Back at Valley Forge, General Washington calls it a fine retreat."
      choices := [] },
    { id := 12, title := "Ending: The Oneida Stand"
      text := "The Oneida warriors give a great war cry from the trees. The dragoons' horses rear and bolt, and the riders do not come back. The rear guard crosses the river. You thank the Oneida chiefs in front of the whole army."
      choices := [] },
    { id := 13, title := "Ending: Cut Off"
      text := "The Oneida do not hear your call in time. The dragoons ride into the rear guard, and many of your men are taken prisoner. You get away across the river, but you leave too many men behind. You will not forget this lesson."
      choices := [] } ]

/-- **Lafayette at Barren Hill is legal for Lafayette.** The Lean kernel runs the checker to
prove it. -/
theorem barren_hill_legal : LegalAdventure rules lafayette barrenHill :=
  check_sound (by decide)

/-- Rule 7 holds for the built-in Adventure: from every Scene, an Ending can be reached. -/
theorem barren_hill_reaches_ending :
    ∀ s ∈ barrenHill.scenes, ReachesEnding barrenHill s.id :=
  barren_hill_legal.2.2.2.2.2

/-- Rule 7 by hand, for one Scene: from Across the Schuylkill (Scene 10), the Fight with the
dragoon leads to the Ending The Rear Guard Holds (Scene 11). -/
example : ReachesEnding barrenHill 10 := by
  apply ReachesEnding.next (t := 11)
  -- The first Choice of Scene 10 is the Fight with the dragoon. A win leads to Scene 11.
  · refine ⟨barrenHill.scenes[10], by simp [barrenHill], rfl, _, List.mem_cons_self, ?_⟩
    simp [Outcome.targets]
  -- Scene 11 has no Choices, so it is an Ending.
  · exact .ending ⟨barrenHill.scenes[11], by simp [barrenHill], rfl, rfl⟩

/-- The built-in Adventure has no loop of 1 to 3 steps (the short-loop rule). -/
theorem barren_hill_no_short_loops : barrenHill.NoShortLoops :=
  barrenHill.checkShortLoops_sound (by decide)

end Rpg.Lafayette
