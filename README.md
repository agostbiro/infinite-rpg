# Infinite RPG

## Overview

A role-playing game (RPG) with AI-generated adventures.

The player types a wish, such as "I love LOTR, give me an adventure set in the Shire", and an AI dungeon master writes an adventure and a character for it. 
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

The Anthropic API key is needed for adventure generation and for changes during play, but you can test without one using an example adventure.
Without it, the Front Page and the "Change the world" panel say that the Dungeon Master is not connected, and you can play The Drowned Lighthouse and the saved Adventures.
`make run-fake` runs the game with recorded replies from `tests/fake-api` instead, and never calls the API.

## Properties

#### Consistency

We formally specify an abstract game system in Lean based on the [Generic Universal Role Playing System (GURPS).](https://en.wikipedia.org/wiki/GURPS)
We know that GURPS is fun and allows for a lot of variety in adventures.

Lean verifies each AI-generated adventure against the [spec.](./Rpg/Spec.lean)
This ensures that the gameplay is consistent between adventures without restricting the creativity of the AI dungeon master.

#### No Dead Ends or Infinite Loops

The adventures are graphs of scenes.
Lean [verifies](./Rpg/Check.lean#L272) that adventures have no dead ends or infinite loops: from every scene, some path of choices leads to an ending.

#### Balance

A consistent adventure with no dead ends or infinite loops can be still be too easy or too hard.
Therefore, we run a [statistical test](./Rpg/Probability/StatisticalAdmission.lean#L205) after verification to check that the death rate on each turn fits a rising curve, so the adventure is balanced.

Lean [proves](./Rpg/Probability/StatisticalAdmission.lean#L155) that the test is sound: it accepts an unbalanced adventure at most 5% of the time.
A Wish gets 3 tries, each with a fresh test, so an unbalanced adventure from a Wish passes at most 15% of the time (a union bound; Lean proves only the bound for one try).
All the changes during play in one server run share one more 5% (`RetryTree.balanced`), so an adventure from a Wish that then gets changes passes unbalanced at most 15% + 5% = 20% of the time.
These bounds hold under the sampling model, as [statistical confidence](docs/statistical-confidence.md) explains.

#### Adjustable Difficulty

We define multiple balance curves to offer a choice of difficulty to the user (easy, medium, hard).

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

Every adventure, built in or from a Wish, gets four combat rules from `defaultCombatRules` in [Rpg/Mechanic.lean](./Rpg/Mechanic.lean):

- **Committed Strike:** All-Out Attack gets +1 damage per hit.
- **Guard Feint:** enemies get -1 to hit a Character who uses All-Out Defense.
- **Cornered Fury:** enemies at half HP or less get +2 to hit.
- **Punish the Opening:** enemies get +1 damage per hit against All-Out Attack.

Play, the balance check, and the exact model use the same Engine for these rules.
The combat buttons show the rules that apply to each maneuver.
The DM prompt lists these rules, and asks for tactics in the Scenes with real roll branches, such as a trap that splits a group.
A change during play keeps every rule that is already there, these four too.

The Drowned Lighthouse has new choices: a bluff at the relief watch, a cargo-net ambush that cuts off one wrecker, a rescue of the keeper that disarms Hollis, a flare bluff, and a new ending.
Each one is a real roll, with a way to fail.

## Balance and lifetime study

The [report](experiments/results/report.html) has charts and tables from 175,000 simulated games: seven variants of two adventures, nine balance-curve settings, 20,000 lifetime runs per variant, and five balance checks of 1,000 games per variant.
The [plan](experiments/plan.json) fixes all seeds and settings.
A different balance curve does not change the game, so all settings use the same games.

Run `python3 scripts/run_balance_study.py`, then make the report with:

```sh
uv run --no-project --with matplotlib==3.11.2 python scripts/report_balance_study.py
```

- The default check rejected the unchecked weapon, the too-strong enemies, and the variants with no fights, in all five batches. With the tolerance widened to ±0.30, every variant passed all five.
- In the new Lighthouse, 67.60% of the games with the random model player ended in death. Characters who died made 4.81 Scene choices on average.
- The default check also passed Silver Acorn, where 83.44% of games end in death. The check looks at when deaths happen in the first turns, not at the overall win rate.

The study only explores. It does not replace the balance check, and it does not prove confidence across all the comparisons at once.
The game still uses its original curve and confidence level.

## Limitations

- No Dead Ends ignores dice, so the character can still die before reaching an ending.
- The spec only says that each fight can end, not that the character can win it.
- Each proof is about one character, so the same adventure can fail for another character.
- The balance test plays with a model player who picks choices and maneuvers at random, not like a real player.
- The 5% bound assumes that the seeded random generator acts like fair dice, and this is not proved.
- An AI-generated adventure gets up to 3 tries, so the chance to accept an unbalanced one is at most 15%.
- A saved adventure skips the balance test on load if its cached verdict file says it passed, so an edited verdict file can skip the test.
- Live adventures trust that the compiled checker gives the same answer as the checker in the proofs.
- The rules were typed in by hand from GURPS Lite, and a person must check them against the book.
- Nothing proves that the game engine follows the rules during a fight.
- The server, the view, and the AI prompt code have no proofs.
- The game covers only part of GURPS Lite: there are no items, no parry, no spells, and creatures always attack.
- The only ranged weapon is the flamethrower, and it has no range rules.

