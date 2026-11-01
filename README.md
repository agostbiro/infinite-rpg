# Infinite RPG

## Overview

A role-playing game (RPG) with AI-generated adventures.

The player types a wish, such as "I love LOTR, give me an adventure set in the Shire", and an AI dungeon master writes an adventure and a character for it. 
The adventure is a 3D world in the browser: the player walks to a door, a boat, or a person to choose what happens next.
Lean verifies a bunch of [properties](#properties) of the generated adventures to make sure the game is fun and challenging.

During gameplay, the player can ask the AI dungeon master for a change in the adventure, such as replacing their sword with a flamethrower.
Lean ensures that the consistency and the difficulty of the game remains unchanged, so the AI has to balance the flamethrower by adding a counter such as a water shield for the opponents.

## Quick Start

Prerequisites: Lean toolchain.

```
make install
export ANTHROPIC_API_KEY=sk-... 
make run
```

This will run the game server. 
Visit [localhost:8080](http://127.0.0.1:8080/) in your browser to play the game.

The Anthropic API key is needed for adventure generation and for changes during play.
Without it, the Front Page and the "Change the world" panel say that the Dungeon Master is not connected, and you can play the saved Adventures.
There is no built-in adventure for now; a new one comes later (see the [follow-ups](docs/follow-ups.md)).
`make run-fake` runs the game with recorded replies from `tests/fake-api` instead, and never calls the API. It has no recorded Wish for now.

## Properties

#### Consistency

We formally specify an abstract game system in Lean based on the [Generic Universal Role Playing System (GURPS).](https://en.wikipedia.org/wiki/GURPS)
We know that GURPS is fun and allows for a lot of variety in adventures.

Lean verifies each AI-generated adventure against the [spec.](./Rpg/Spec.lean)
This ensures that the gameplay is consistent between adventures without restricting the creativity of the AI dungeon master.

#### No Dead Ends or Infinite Loops

The adventures are graphs of scenes.
Lean [verifies](./Rpg/Check.lean#L272) that adventures have no dead ends or infinite loops: from every scene, some path of choices leads to an ending.

#### No Short Loops

A path of choices may lead back to a scene that the player already saw, but not too soon.
Lean [proves](./Rpg/EventGraph.lean#L63) that if the check passes, every loop has at least 4 steps, so the player sees at least 3 other scenes before a scene comes back.
The check counts every outcome, also an unlikely roll, and every Wish and every change during play must pass it.

#### Balance

A consistent adventure with no dead ends or infinite loops can be still be too easy or too hard.
Therefore, we run a [statistical test](./Rpg/Probability/StatisticalAdmission.lean#L206) after verification to check that the death rate on each turn fits the rising curve of the adventure's [difficulty level](#adjustable-difficulty), within 5 percentage points, so the adventure is balanced.
The test plays the adventure 1,200 times.

Lean [proves](./Rpg/Probability/StatisticalAdmission.lean#L156) that the test is sound: it accepts an unbalanced adventure at most 5% of the time.
A Wish gets 3 tries, each with a fresh test, so an unbalanced adventure from a Wish passes at most 15% of the time (a union bound; Lean proves only the bound for one try).
All the changes during play in one server run share one more 5% (`RetryTree.balanced`), so an adventure from a Wish that then gets changes passes unbalanced at most 15% + 5% = 20% of the time.
These bounds hold under the sampling model, as [statistical confidence](docs/statistical-confidence.md) explains.

#### Adjustable Difficulty

The player picks a difficulty level in the Wish form: easy, medium (the default), or hard.
Each level is its own balance curve. The curves differ in how many characters are still alive after 10 turns:

| Level  | Alive after 10 turns | Death on turn 1 | Death on turn 6, given alive at turn 4 |
|--------|----------------------|-----------------|----------------------------------------|
| easy   | 50%                  | 0.7%            | 6.9%                                   |
| medium | 30%                  | 1.2%            | 11.1%                                  |
| hard   | 10%                  | 2.3%            | 18.2%                                  |

The balance test checks every row against the curve of the chosen level, with a tolerance of 5 percentage points.
The DM prompt gives the DM the allowed range of each row for that level.
`make validate` prints the target of every row for each level.

The level is saved with the adventure (`difficulty` in `adventure.json`) and shown on its card.
It stays the same for the life of the adventure: a change during play is checked against the same curve, and Lean [proves](./Rpg/WorldChange.lean) that a change cannot change the level (`live_change_policy`).
Lean also proves that the levels are valid curves (`difficulty_valid`), and that hard < medium < easy in survival at turn 10 (`difficulty_order`).

An adventure saved before the levels existed counts as medium, so it is checked again at medium on load.
The test Adventure (The Bandit Camp) fails medium. It keeps the old curve with a tolerance of 20 points until a new default Adventure that passes medium takes its place (see [follow-ups](docs/follow-ups.md)).

## How a change during play becomes part of the game

During play, use **Change the world** to ask for a weapon, a combat effect, or another supported
change to the Adventure. The DM (Dungeon Master) proposes the rule you asked for and a fun counter-rule together.
The server checks the changed Adventure from its start, and keeps your current HP and position.
If a proposal fails, the DM revises it. One change gets at most 6 proposals, 3 balance checks,
and 3 minutes. Each proposal can use up to 3 tries when the API server is busy. At the time limit,
the server stops the DM at once, also during a slow call. Then the change fails, and your game is unchanged. "Cancel" stops it
earlier. Your game stays paused and unchanged until a change passes.
The current Fight, wounds, choices, history, and game dice stay the same. New rules appear
in the story and in "Rules of this world". A change belongs to this playthrough only. It is not
saved, and "Play again" and "← Adventures" use the original Adventure. See
[live rule changes](docs/live-rule-changes.md).

The sampled games of the balance check stop after 6 turns. A change can add or replace a Scene that is not visited yet. If that Scene is more than 6 turns from the start, its new encounters get only the legality check, not the balance check. This gap is open; [ADR 0005](docs/adr/0005-live-rule-changes.md) lists it with the other known gaps.

## Shared tactics and new choices

Every adventure gets four combat rules from `defaultCombatRules` in [Rpg/Mechanic.lean](./Rpg/Mechanic.lean):

- **Committed Strike:** All-Out Attack gets +1 damage per hit.
- **Guard Feint:** enemies get -1 to hit a Character who uses All-Out Defense.
- **Cornered Fury:** enemies at half HP or less get +2 to hit.
- **Punish the Opening:** enemies get +1 damage per hit against All-Out Attack.

Play, the balance check, and the exact model use the same Engine for these rules.
The combat buttons show the rules that apply to each maneuver.
The DM prompt lists these rules, and asks for tactics in the Scenes with real roll branches, such as a trap that splits a group.
A change during play keeps every rule that is already there, these four too.

The test adventure, The Bandit Camp, has such choices: a bluff at the gate, a cargo-net ambush that cuts off one bandit, a rescue that disarms the chief, a bluff about the guards, and three endings.
Each one is a real roll, with a way to fail.

## Limitations

- No Dead Ends ignores dice, so the character can still die before reaching an ending.
- The spec only says that each fight can end, not that the character can win it.
- Each proof is about one character, so the same adventure can fail for another character.
- The balance test plays with a model player who picks choices and maneuvers at random, not like a real player.
- The 5% bound assumes that the seeded random generator acts like fair dice, and this is not proved.
- The test Adventure is exempt from the medium curve: it uses the old curve with a tolerance of 20 points.
- An AI-generated adventure gets up to 3 tries, so the chance to accept an unbalanced one is at most 15%.
- A saved adventure skips the balance test on load if its cached verdict file says it passed, so an edited verdict file can skip the test.
- Live adventures trust that the compiled checker gives the same answer as the checker in the proofs.
- The rules were typed in by hand from GURPS Lite, and a person must check them against the book.
- Nothing proves that the game engine follows the rules during a fight.
- The server, the view, and the AI prompt code have no proofs.
- The game covers only part of GURPS Lite: there are no items, no parry, no spells, and creatures always attack.
- The only ranged weapon is the flamethrower, and it has no range rules.

Work that is still open is in the [follow-ups](docs/follow-ups.md).
