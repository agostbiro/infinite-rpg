# Infinite RPG

## Overview

A role-playing game (RPG) with AI-generated adventures.

The player types a wish, such as "I love Lord of the Rings, give me an adventure set in the Shire", and an AI dungeon master writes an adventure and a character for it. 
The adventure is a 3D world in the browser: the player walks to a door, a boat, or a person to choose what happens next.
Lean verifies a bunch of [properties](#properties) of the generated adventures to make sure the game is fun and challenging.

During gameplay, the player can ask the AI dungeon master for a change in the adventure, such as replacing their sword with a flamethrower.
Lean checks the changed adventure again, so the AI must keep it consistent and balanced, for example by giving the opponents a water shield.

## Demo

The [demo video](https://youtu.be/gulcJwxCdkI) (4.5 minutes) shows live gameplay: it creates a new adventure, plays it, and swaps the hero's sword for a light sabre.
It also explains what Lean verifies and how.

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
So after verification we play 1200 sample games and run a [statistical test](./Rpg/Probability/StatisticalAdmission.lean#L102) to check that the death rate in the first 6 turns fits a curve where danger rises over time.

Lean [proves](./Rpg/Probability/StatisticalAdmission.lean#L160) that the test is sound: if the sample games act like independent random games, the test accepts an adventure that is off the curve at most 5% of the time.

## Limitations

- The server does not run the combat check yet. The check solves each Fight at each starting HP and gives its exact exit law. On Lafayette it takes about 4 to 5 seconds with 14 cores, and 28 seconds on one core ([exact exit laws](docs/exact-exit-laws.md)). The server starts the built-in Adventure, Wishes, saved Adventures, and live changes after the balance check only. One exception: a live change during a Fight also checks the paused Fight (`checkContinuation`), before it spends a validation batch and a part of the error allowance. Above a size limit (`SolveBudget`) that check gives up and rejects the change, and the message names the Creatures of the paused Fight and says why it failed (`PausedFightFailure.message`); with Creatures like Lafayette's Grenadiers (ST 11), a Fight with 3 or 4 of them, or with a flamethrower against 2 or more, is above it. On the Fights measured in that note, one check that rejects takes at most about 18 seconds on one core, and one that passes up to about 35 seconds; the Dungeon Master may then revise the counter-rules, and each revision is checked again. The server does not check the same equipment and rules twice, also when a proposal changes only Scenes: it remembers each check that failed, and reuses each check that passed. If the last proposal still fails the check, the change ends with a message that says the paused Fight could not be checked. `make certify` runs the combat check on Lafayette by hand. The theorem `admitted_combats` is about Adventures that passed it.
- Cancel and the live-change time limit prevent a late change from being installed, but they do not stop a check of a paused Fight already running inside Lean. Such workers can keep using CPU and memory after cancellation, and another request can start additional work. The three-minute limit is not a computation or resource limit.
- No Dead Ends ignores dice, so the character can still die before reaching an ending.
- The combat check (`make certify`) proves probability-one termination under fair independent dice and the uniform combat policy, with a finite horizon for every positive failure allowance. It does not guarantee victory or termination under every player strategy.
- Each proof is about one character, so the same adventure can fail for another character.
- The balance test plays with a model player who picks choices and maneuvers at random, not like a real player.
- The 5% bound assumes that the seeded random generator acts like fair dice, and this is not proved.
- A wish gets at most five attempts, including Retry, and each try runs the full 5% test. Under the sampling assumptions, a union bound gives at most 25% false acceptance per wish. Starting a new wish starts a new limit. Changes during play share one 5% budget, and Lean [proves](./Rpg/Probability/Retry.lean#L59) this bound.
- A saved adventure skips the balance test on load if its cached verdict file says it passed, so an edited verdict file can skip the test.
- Live adventures trust that the compiled checker gives the same answer as the checker in the proofs.
- The combat certificate (`CertifiedFight`) is checked against a fast round (`fastProcess` and the definitions in `Rpg/Probability/FastCombat.lean`), and uses `Std.HashMap` and parallel tasks. The theorems are still about the spec round (`combatProcess`), because `fastRound_expect` proves the two have the same odds. They decide only which certificates exist, so a reviewer need not read them for soundness. The graph (`adventureGraph`) gives a `stalled` edge to a Fight that fails this check (`checkedCombat`). There the solver has no budget, so the odds that the balance theorems are about do not depend on the budget. This puts the solver (`solveFight` and everything it calls, such as `planRounds`, `batchesBy`, `keepReachable`, `groupAnswers`, `solveGroup`, `attackBounds` and `roundSizeBound`) inside the definition of those odds, so a reviewer of `BalancedAt` should read it too.
- The rules were typed in by hand from GURPS Lite, and a person must check them against the book.
- Combat certificates check normalized outcome equations against the shared fight engine. Human review is still needed to compare that engine with the intended GURPS rules.
- The server, the view, and the AI prompt code have no proofs.
- The game covers only part of GURPS Lite: there are no items, no parry, no spells, and creatures always attack.
