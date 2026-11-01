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

## 9. One skill for each kind of Survival and Riding

**GURPS Lite (p. 16-17):** There are many types of Survival skill (one per kind of land), each learned on its own. Riding is the skill of one kind of mount.

**This game:** Survival is one skill for every kind of land, and Riding is one skill for every mount.

**Reason:** The Adventure, not the rules, says where the Character is and what it rides. One skill keeps the skill list short for the DM.

**Follow-up task:** Add specialties to `Skill`, such as Survival (Woodlands), and let a roll name one.

## 10. Influence skills are plain Success Rolls

**GURPS Lite (p. 15):** To make a Creature do something with Fast-Talk or Diplomacy, you win a Quick Contest of the skill against the Creature's Will. A failed Fast-Talk roll gives a bad reaction.

**This game:** A Fast-Talk or Diplomacy Choice is a Success Roll at a modifier that the DM picks. The failure branch is the bad reaction.

**Reason:** v0 has no Quick Contests (see the scope in `README.md`).

**Follow-up task:** Make influence Choices a Quick Contest against the Creature's Will, with deviation 8 for a tie.

## 11. The quarterstaff has one attack mode

**GURPS Lite (p. 20):** A quarterstaff can swing (sw+2 crushing) or thrust (thr+2 crushing), with Staff skill or Two-Handed Sword skill. It needs two hands, and Staff skill gives +2 to Parry.

**This game:** The quarterstaff only swings, for sw+2 crushing, and only with Staff skill. Two hands have no effect, because a being has one weapon and no shield. There is no Parry in v0, so the +2 to Parry has no effect.

**Reason:** Each weapon has one attack mode in v0.

**Follow-up task:** Add attack modes and Parry, then add the thrust and the Parry bonus.

## 12. Swimming, Climbing, and First Aid are only story rolls

**GURPS Lite (p. 14, 17, 22, 30):** A Swimming roll is against the higher of HT or Swimming when you avoid fatigue or injury in water. Climbing has rules for speed. First Aid restores HP (Recovery, p. 30). First Aid has a tech level (TL).

**This game:** Each of these is a plain Success Roll against the skill level (learned, or the default). A roll changes only which Scene comes next. First Aid does not restore HP, and tech levels do not exist.

**Reason:** In v0 the Character's HP change only in Fights, and there is no movement or fatigue.

**Follow-up task:** Let a Scene heal the Character after a First Aid roll, by the Recovery rules.

## 13. The flamethrower sprays every Creature

**GURPS Basic Set (not in GURPS Lite):** A flamethrower is a ranged weapon with Liquid Projector skill. It fires a jet at one target, or sweeps an area by the area-attack rules.

**This game:** The flamethrower does 3d burning damage whatever the user's ST, and needs ST 10. Each attack with it is a spray: the attacker rolls a separate attack against each living Creature, in list order. Each Creature may Dodge. Burning injury is the damage that gets past DR, with no multiplier, and the lowest basic damage is 1. There is no range, ammunition, or fire that goes on burning.

**Reason:** There is no map and no range in this game. One spray attack per foe is the simple form of an area attack.

## 14. The balance model's Player picks maneuvers at random

**GURPS Lite:** The rules say nothing about how a Player picks a maneuver.

**This game:** This is not a change to play. The Player in the browser picks each maneuver. The balance check (`Rpg/Probability/`) needs a model of a Player, so its Player picks Attack, All-Out Attack, or All-Out Defense with chance 1/3 each, and then a living target at random. It also picks each Choice in a Scene at random.

**Reason:** A fixed and simple model of the Player keeps the balance check exact and easy to review. Real Players can do better or worse than it.

## 15. Adventure rules can change during play

**This game:** A Player can request an adventure-local rule change. The DM can grant a named
weapon profile or combat effect, add conditional counter-rules, and revise unvisited scenes.
Weapon profiles specify attack level and damage dice. Combat effects can add to hit rolls,
damage, or armor when an HP, maneuver, or equipment condition holds. These effects are
house rules, not a claim to implement GURPS equipment construction or advantages.

**Reason:** Player requests should create new tactical decisions in the current world.
The shared Engine applies the same effects in play and balance sampling. The fixed core
rules, wounds, history, and unfinished Fight remain. A source-bound check from the updated adventure beginning must
pass before any change applies. See [live rule changes](live-rule-changes.md) for the supported
language, retry theorem, and limits.

## Shared tactical defaults

All authored and generated adventures now inherit `defaultCombatRules`: Committed Strike
adds 1 damage to the Character's All-Out Attack; Guard Feint reduces enemy hit level by 1
against All-Out Defense; Cornered Fury adds 2 to enemy hit level at half HP or less; and
Punish the Opening adds 1 enemy damage against All-Out Attack. These extend the shared
GURPS-derived rules, rather than being Lighthouse-only effects. The original maneuver costs,
Dodge restrictions, dice, HP, damage types, and character budgets remain in force.

The player decision is whether to commit to a finishing blow, guard against retaliation,
or finish a wounded enemy before it rallies. The log names each effect when it fires, and
the buttons preview relevant effects. Fun is a design judgment; the balance theorem checks
the conditional death intervals under the fixed random-player policy.

Lighthouse's environmental tactics use the existing roll/fight graph language. A successful
cargo-net roll leads to a one-wrecker fight; a successful keeper-rescue roll leads to a fight
against knife-armed Hollis or a flare bluff. Failed attempts lead to ordinary confrontation.
The shared GM prompt requests comparable real branches in newly generated adventures.
