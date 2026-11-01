# Infinite RPG

## Overview

A role-playing game (RPG) with AI-generated adventures.

The player types a wish, such as "I love LOTR, give me an adventure set in the Shire", and an AI dungeon master writes an adventure and a character for it. 
Lean verifies a bunch of [properties](#Properties) of the generated adventures to make sure the game is fun and challenging.

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

The Antrhopic API key is needed for adventure generation, but you can test without one using an example adventure.

## Properties

#### Consistency

We formally specify an abstract game system in Lean based on the [Generic Universal Role Playing System (GURPS).](https://en.wikipedia.org/wiki/GURPS)
We know that GURPS is fun and allows for a lot of variety in adventures.

Lean verifies each AI-generated adventure against the [spec.](./Rpg/Spec.lean)
This ensures that the gameplay is consistent between adventures without restricting the creativity of the AI dungeon master.

#### No Dead Ends or Infinite Loops

The adventures are graphs of scenes.
Lean [verifies](./Rpg/Check.lean#L257) that adventures have no dead ends or infinite loops: from every scene, some path of choices leads to an ending.

#### Balance

A consistent adventure with no dead ends or infinite loops can be still be too easy or too hard.
Therefore, we run a [statistical test](./Rpg/Probability/StatisticalAdmission.lean#L150) after verification to check that the death rate on each turn fits a rising curve, so the adventure is balanced.

Lean [proves](./Rpg/Probability/StatisticalAdmission.lean#L109) that the test is sound: it accepts an unbalanced adventure at most 10% of the time.

#### Adjustable Difficulty

We define multiple balance curves to offer a choice of difficulty to the user (easy, medium, hard).

## Limitations

- No Dead Ends ignores dice, so the character can still die before reaching an ending.
- The spec only says that each fight can end, not that the character can win it.
- Each proof is about one character, so the same adventure can fail for another character.
- The balance test plays with a model player who picks choices and maneuvers at random, not like a real player.
- The 10% bound assumes that the seeded random generator acts like fair dice, and this is not proved.
- An AI-generated adventure gets up to 3 tries, so the chance to accept an unbalanced one is at most 30%.
- A saved adventure skips the balance test on load if its cached verdict file says it passed, so an edited verdict file can skip the test.
- Live adventures trust that the compiled checker gives the same answer as the checker in the proofs.
- The rules were typed in by hand from GURPS Lite, and a person must check them against the book.
- Nothing proves that the game engine follows the rules during a fight.
- The server, the view, and the AI prompt code have no proofs.
- The game covers only part of GURPS Lite: there are no items, no parry, no spells, and creatures always attack.
- The only ranged weapon is the flamethrower, and it has no range rules.

