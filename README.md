# Infinite RPG

## Overview

A role-playing game (RPG) with AI-generated adventures.

The player types a wish, such as "I love Lord of the Rings, give me an adventure set in the Shire", and an AI dungeon master writes an adventure and a character for it. 
The adventure is a 3D world in the browser: the player walks to a door, a boat, or a person to choose what happens next.
Lean verifies a bunch of [properties](#properties) of the generated adventures to make sure the game is fun and challenging.

During gameplay, the player can ask the AI dungeon master for a change in the adventure, such as replacing their sword with a flamethrower.
Lean checks the changed adventure again, so the AI must keep it consistent and balanced, for example by giving the opponents a water shield.

## Quick Start

Prerequisites: `make`, `git`, and `curl`. `make install` installs Lean.

```
make install
export ANTHROPIC_API_KEY=sk-... 
make run
```

This will run the game server. 
Visit [localhost:8080](http://127.0.0.1:8080/) in your browser to play the game.

The built-in adventure, Lafayette at Barren Hill, plays without a key: click its card on the front page.
The Anthropic API key is needed for adventure generation and for changes during play.
Without it, the front page and the "Change the world" panel say that the dungeon master is not connected, and you can play the built-in adventure and the saved adventures.
`make run-fake` runs the game with recorded replies from `tests/fake-api` instead, and never calls the API. It has no recorded wish for now.

## Properties

The built-in adventure passes the first three checks below when Lean builds the game, and the balance test when the server starts.
Every new adventure from a wish and every change during play must pass all four checks.

#### Consistency

We formally specify an abstract game system in Lean based on the [Generic Universal Role Playing System (GURPS).](https://en.wikipedia.org/wiki/GURPS)
GURPS is a well-known and flexible system that allows for a lot of variety in adventures.

Lean verifies each AI-generated adventure against the [spec.](./Rpg/Spec.lean)
For example, every creature and the character must be legal GURPS builds, the character must be able to try every roll, and every fight must be able to end.
This ensures that the gameplay is consistent between adventures without restricting the creativity of the AI dungeon master.

#### No Dead Ends

The adventures are graphs of scenes.
Lean [verifies](./Rpg/Check.lean#L296) that adventures have no dead ends: from every scene, some path of choices leads to an ending.

#### No Short Loops

A path of choices may lead back to a scene that the player already saw, but not too soon.
Lean [proves](./Rpg/EventGraph.lean#L63) that if the check passes, every loop has at least 4 steps, so the player sees at least 3 other scenes before a scene comes back.

#### Balance

A consistent adventure with no dead ends can still be too easy or too hard.
So after verification we play 1200 sample games and run a [statistical test](./Rpg/Probability/StatisticalAdmission.lean#L96) to check that the death rate in the first 6 turns fits a curve where danger rises over time.

Lean [proves](./Rpg/Probability/StatisticalAdmission.lean#L154) that the test is sound: if the sample games act like independent random games, the test accepts an adventure that is off the curve at most 5% of the time.

## Limitations

- No Dead Ends ignores dice, so the character can still die before reaching an ending.
- The spec only says that each fight can end, not that the character can win it.
- Each proof is about one character, so the same adventure can fail for another character.
- The balance test plays with a model player who picks choices and maneuvers at random, not like a real player.
- The 5% bound assumes that the seeded random generator acts like fair dice, and this is not proved.
- A wish gets up to 3 tries, and each try runs the full 5% test, so one wish request accepts an unbalanced adventure at most 15% of the time. Each retry adds to this. Changes during play share one 5% budget, and Lean [proves](./Rpg/Probability/Retry.lean#L59) this bound.
- A saved adventure skips the balance test on load if its cached verdict file says it passed, so an edited verdict file can skip the test.
- Live adventures trust that the compiled checker gives the same answer as the checker in the proofs.
- The rules were typed in by hand from GURPS Lite, and a person must check them against the book.
- Nothing proves that the game engine follows the rules during a fight.
- The server, the view, and the AI prompt code have no proofs.
- The game covers only part of GURPS Lite: there are no items, no parry, no spells, and creatures always attack.
