# Verified RPG

A single-player tabletop role-playing game (RPG) based on GURPS. An AI writes the adventures, and each adventure must pass a check against the game rules before anyone can play it.

## People and parts

**DM** (Dungeon Master):
The AI that writes an Adventure and its Character. During play, it can propose a World change, which is installed only after the checks pass. It never picks a die face.
_Avoid_: GM, narrator, agent

**Player**:
The human who plays an Adventure.
_Avoid_: user

**Engine**:
The part of the game that applies the rules during play. It rolls all dice and works out every result.
_Avoid_: interpreter, runtime

**Report**:
One thing the Engine did or found out during play, shown to the Player, such as "rolled 11, success" or "Mara hits the Drowned Man for 6".
_Avoid_: event, log line, message

## Adventures

**Adventure**:
A scenario represented as a graph of Scenes. Checked live changes can revise its future scenes and local rules.
_Avoid_: module, campaign, scenario

**Wish**:
The text the Player types to ask the DM for an Adventure, such as "I love LOTR, set it in the Shire".
_Avoid_: prompt, request, query

**Front Page**:
The page where the Player chooses an Adventure to play or makes a Wish.
_Avoid_: title screen, home page, menu

**Test Adventure**:
A small Adventure, The Bandit Camp, for the tests and the example theorems. The server never offers it for play.
_Avoid_: sample, demo adventure

**Legal Adventure**:
An Adventure that obeys every rule in the spec, under its RuleSet. Only a Legal Adventure can be played.
_Avoid_: valid adventure, verified adventure

**RuleSet**:
The rules of one Adventure: core limits and functions, plus local equipment and combat effects. Live changes can modify the local data; core limits and functions remain fixed.
_Avoid_: ruleset config, house rules

**Balance**:
The property that the balance check tests: the deaths on each turn of an Adventure fit a rising target curve. The check is a statistical test, so it can pass an unbalanced Adventure at most 5% of the time.
_Avoid_: fairness

**Admission**:
The balance check that an Adventure must pass after the checker, before play and before a World change is installed. It plays the Adventure 1,200 times from its start with a seed, and compares the deaths on each turn with the target curve of its Difficulty level.
_Avoid_: certification, validation (except for the run with the fixed seed)

**Difficulty level**:
How dangerous an Adventure is: easy, medium, or hard. The Player picks it before a Wish. Each level is a target curve for the balance check, with a tolerance of 5 percentage points. An Adventure keeps its level for its whole life. An Adventure with no level is medium.
_Avoid_: difficulty profile, mode

**Horizon**:
How many turns after the first one the balance check looks at. With horizon 5, it looks at turns 1 to 6.
_Avoid_: window size

**World**:
The setting of an Adventure in a few words, such as "Middle-earth, the Shire". It changes only what the Player sees, never what the rules do.
_Avoid_: universe, setting, genre

**Intro**:
The short text the Player reads before the first Scene. It names the world of the Adventure and says who the Character is. It changes only what the Player sees, never what the rules do.
_Avoid_: blurb, premise, synopsis

**Scene**:
One step of an Adventure: some text and a list of Choices.
_Avoid_: room, node, page

**3D world**:
The page shows the Adventure as a landscape. The Player walks to a marked object or person to pick a Choice or a Maneuver. Each object sends one input that the game offers, unchanged. It changes only what the Player sees, never what the rules do.
_Avoid_: level, room

**World map**:
The places, paths, and props of an Adventure, and the place of each Scene. The DM draws it in a separate request after the Adventure passes its checks. It changes only what the Player sees, never what the rules do.
_Avoid_: level, layout

**Journal**:
The text of the story, the Character, and one button for each input, next to the 3D world. Without WebGL, the page shows only the journal.
_Avoid_: log, transcript

**Theme Name**:
A name an Adventure gives to a skill or a piece of Gear, shown to the Player in place of the rule name. For example, Broadsword shows as "Wand Duelling". It changes only what the Player sees, never what the rules do.
_Avoid_: alias, label, reskin

**Choice**:
An option the Player can pick in a Scene. It leads to another Scene, either directly or through a Test.
_Avoid_: action, option, exit

**Ending**:
A Scene with no Choices. Reaching it ends the Adventure. The Character's death also ends the Adventure, but it is not an Ending.
_Avoid_: victory, conclusion, terminal scene

**Loop**:
A path of Choices that comes back to the Scene where it started. Each Scene that an Outcome can lead to counts as a step, whatever the dice do. Every Loop must have at least 4 steps (No Short Loops).
_Avoid_: cycle, non-cyclic, equilibrium

**Item**:
A story thing the Character carries from Scene to Scene, such as a key or a letter. A Choice can require an Item. Weapons and armor are Gear, not Items.
_Avoid_: object, loot, inventory entry

**Gear**:
The weapon and armor a Character or Creature uses. A checked live change can grant new weapon Gear.
_Avoid_: equipment, kit, loadout

**World change**:
A change that the Player asks for during play, such as a new weapon, together with a Counter-rule. The two are installed together, only after the checker and the Admission of the changed Adventure from its start pass. It is not saved.

**Counter-rule**:
A named, visible response to a requested change that adds a tactical choice. The DM proposes one from the first attempt, even if the gift would already pass the balance check.

**Flag**:
A record that an event happened, such as "the guard is bribed". A Scene can set a Flag, and a Choice can require one.
_Avoid_: variable, state bit, quest marker

**Test**:
A point where dice decide what happens next: a Success Roll, a Quick Contest, or a Fight. Each Test has one branch for success and one for failure.
_Avoid_: check, roll, challenge

## Beings

**Character**:
The being the Player controls.
_Avoid_: PC, hero, avatar

**Creature**:
Any being in an Adventure other than the Character, such as a monster or an NPC (non-player character).
_Avoid_: monster, enemy, mob

## Rules

**Success Roll**:
A roll of 3d6 against a skill or attribute. It succeeds if the total is at or below the target number.
_Avoid_: skill check, ability check

**Quick Contest**:
Two beings each make a Success Roll. The one who succeeds by more wins.
_Avoid_: opposed roll

**Fight**:
Melee combat between the Character and one or more Creatures, run turn by turn by the Engine.
_Avoid_: combat encounter, battle

**Maneuver**:
What a being chooses to do on its turn in a Fight: Attack, All-Out Attack, or All-Out Defense. The maneuver also sets the being's defense until its next turn.
_Avoid_: action, combat option

- **Shared meta rules:** `defaultCombatRules`, inherited by every new adventure through
  `RuleSet`. They include Committed Strike, Guard Feint, Cornered Fury, and Punish the Opening.
- **Death-conditional mean:** average scene-choice turns among sampled characters who died;
  successful endings are excluded. It must be read alongside the death rate.
- **Policy sensitivity study:** replaying the admission comparison on fixed observations
  under different Weibull targets, tolerance, and confidence. It does not change those
  observations or certify every comparison simultaneously.
