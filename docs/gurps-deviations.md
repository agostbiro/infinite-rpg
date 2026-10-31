# Deviations from GURPS Lite

This file lists each place where the game rules differ from GURPS Lite (Fourth Edition, 2020), with the reason and a possible follow-up task.

These entries describe the full v1 design. The current v0 version leaves out more rules, such as shock, Parry, and Quick Contests. See the scope section of `README.md`.

## 1. A being at 0 HP or less is dead

**GURPS Lite (p. 29-30):** At 0 HP or less, a being rolls HT each turn (at -1 per full multiple of HP below zero) or falls unconscious. At -1×HP and at each further multiple, it rolls HT or dies. A failure by only 1 or 2 is a mortal wound, not death. At -5×HP it dies with no roll.

**This game:** A being at 0 HP or less is dead. There is no unconsciousness, there are no death checks, and there are no mortal wounds.

**Reason:** One threshold is simpler to build and to prove. The cost is that Fights are shorter and deadlier than in GURPS.

**Follow-up task:** Add the full GURPS Lite low-HP rules: HT rolls for consciousness at 0 HP or less, death checks at each multiple of -HP, and automatic death at -5×HP. Then add a "lose but survive" ending to Fights, so an Adventure can send an unconscious Character to a "captured" Scene.

## 2. The Character cannot flee a Fight

**GURPS Lite:** A being can move away from a fight. Retreat depends on movement and position on a map.

**This game:** A Fight ends only when every Creature is dead (Win) or the Character is dead (Death). There is no retreat.

**Reason:** Scenes have no map, so the GURPS movement rules do not apply. A retreat rule would have to be invented.

**Follow-up task:** Let a Fight offer a retreat. One possible rule: a Quick Contest of Basic Speed against the fastest Creature. On a loss, each Creature gets a free attack first. A successful retreat leads to a "fled" Scene that the Adventure must provide.

## 3. No major wounds

**GURPS Lite (p. 30):** A single injury of more than half a being's HP is a major wound. The being rolls HT. On a failure, it is stunned and knocked down: it falls prone and drops what it holds. On a failure by 5 or more, or a critical failure, it falls unconscious.

**This game:** A major wound has no extra effect. Shock still applies.

**Reason:** Knockdown needs posture rules, a "drop and pick up the weapon" rule, and a stun state. The unconscious result conflicts with deviation 1.

**Follow-up task:** Add major wounds together with the follow-up for deviation 1, because both need unconsciousness. Stun, posture (prone, kneeling, standing), and the Change Posture and Ready maneuvers come with it.

## 4. No Fatigue Points

**GURPS Lite (p. 31):** A being has FP equal to its HT. A battle that lasts more than 10 seconds costs 1 FP plus the encumbrance level. Below 1/3 FP, Move, Dodge, and ST are halved. At 0 FP or less, the being must make Will rolls to act. At -1×FP it falls unconscious.

**This game:** There are no FP. Fights cost nothing beyond HP.

**Reason:** In this game only long Fights would cost FP, so FP would be a second resource with little use. The unconscious result also conflicts with deviation 1.

**Follow-up task:** Add FP with the combat cost and the low-FP effects. Do this after the follow-up for deviation 1, because 0 FP and -1×FP need unconsciousness.

## 5. No encumbrance

**GURPS Lite (p. 22):** A being's load, compared to its Basic Lift (ST×ST/5 lb), sets an encumbrance level from 0 to 4. Each level gives -1 to Dodge and to some skills, such as Stealth, and lowers Move. For example, leather armor (19.5 lb) and a broadsword (3 lb) give Light encumbrance (level 1) at ST 10.

**This game:** Gear has no weight. Every being has encumbrance level 0.

**Reason:** It keeps Gear and Dodge simple in v1.

**Follow-up task:** Give each Gear item its weight from the GURPS Lite tables. Compute each being's encumbrance level from its Gear and ST, and apply the penalty to Dodge and Stealth. Gear does not change during an Adventure, so this is one number per being.

## 6. Fewer All-Out options

**GURPS Lite (p. 25-26):** All-Out Attack has three options: Determined (+4 to hit), Double (two attacks), and Strong (+2 damage). All-Out Defense has two options: Increased Defense (+2 to one active defense) and Double Defense (a second, different defense if the first fails).

**This game:** All-Out Attack is always Determined. All-Out Defense is always Increased Defense.

**Reason:** It keeps the Fight menu small.

**Follow-up task:** Add All-Out Attack (Double), All-Out Attack (Strong), and All-Out Defense (Double Defense) to the Fight menu.

## 7. A roll at effective skill below 3 fails

**GURPS Lite (p. 2):** A being cannot attempt a success roll if its effective skill is below 3, except for a defense roll.

**This game:** The Engine does not roll. The Test takes its failure branch.

**Reason:** A Test always has a result, so play can always go on.

**In v0:** The spec requires that the Character can try every roll in an Adventure (`CanTryRoll`). So in a Legal Adventure this case never happens for the Character. It can still happen for a Creature's attack.

**Follow-up task:** None needed. If the rule must match GURPS exactly, show the Choice as unavailable instead, and make the dead-end check use each Character's effective skill.

## 8. A Quick Contest tie counts as a failure

**GURPS Lite (p. 3):** In a Quick Contest, a tie means nobody wins. For Influence rolls (p. 24), such as Diplomacy, any result other than a win counts as a failure.

**This game:** In every Quick Contest, the Character must win outright. A tie takes the failure branch.

**Reason:** A Test has only a success branch and a failure branch.

**Follow-up task:** Let a Quick Contest Test give a third branch for a tie, except for Influence rolls.
