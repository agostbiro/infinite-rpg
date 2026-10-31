# Verified RPG

A single-player tabletop role-playing game (RPG) based on GURPS. An AI writes the adventures, and each adventure must pass a check against the game rules before anyone can play it.

## People and parts

**DM** (Dungeon Master):
The AI agent that writes an Adventure. It works before play and takes no part in play.
_Avoid_: GM, narrator, agent

**Player**:
The human who plays an Adventure.
_Avoid_: user

**Engine**:
The part of the game that applies the rules during play. It rolls all dice and works out every result.
_Avoid_: interpreter, runtime

## Adventures

**Adventure**:
A complete scenario the DM writes before play, as a graph of Scenes. It cannot change once play starts.
_Avoid_: module, campaign, scenario

**Legal Adventure**:
An Adventure that obeys every rule in the spec. Only a Legal Adventure can be played.
_Avoid_: valid adventure, verified adventure

**Scene**:
One step of an Adventure: some text and a list of Choices.
_Avoid_: room, node, page

**Choice**:
An option the Player can pick in a Scene. It leads to another Scene, either directly or through a Test.
_Avoid_: action, option, exit

**Ending**:
A Scene with no Choices. Reaching it ends the Adventure. The Character's death also ends the Adventure, but it is not an Ending.
_Avoid_: victory, conclusion, terminal scene

**Item**:
A story thing the Character carries from Scene to Scene, such as a key or a letter. A Choice can require an Item. Weapons and armor are Gear, not Items.
_Avoid_: object, loot, inventory entry

**Gear**:
The weapon and armor a Character or Creature uses. Gear does not change during an Adventure.
_Avoid_: equipment, kit, loadout

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
