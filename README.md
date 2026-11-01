# Verified RPG

A single-player RPG (role-playing game) based on GURPS Lite, played in the browser. An AI DM (Dungeon Master) writes the adventures, and Lean checks each one against the game rules before anyone can play it. If the DM cheats in the Adventure or in its proof, `make check` fails.

```
make install
make run              # play: opens http://127.0.0.1:8080/ in your browser
make run SEED=7       # the first game uses dice seed 7, so you can replay it
make run PORT=9000    # use another port
make run HOST=10.211.55.6   # listen on this IPv4 (Internet Protocol version 4) address, for example to play from the host of a VM (virtual machine)
make cheats           # watch the checker catch a cheating DM
make check            # build, then replay every proof through the Lean kernel
```

## How to play

`make run` builds the game, starts the server, and opens the page. Ctrl-C stops the server.
Click "Begin". Read the Scene and click a Choice. Some Choices make a Success Roll: the dice tumble, then show the faces the Engine rolled.
In a Fight, the Creatures act, then you click a Maneuver. If you attack and more than one Creature is alive, their cards light up: click the one to attack. "Skip" shows the rest of a turn at once.
The Character panel shows attributes, skills, Gear, and HP. The map shows the Scenes you visited and a "?" for each way you have not taken.
The game ends at an Ending, or when the Character dies, which is not an Ending. "Play again" starts a new game with a new seed. The seed is in the corner.

## How the game runs

- The browser draws, and Lean decides (see `docs/adr/0002-browser-draws-lean-decides.md`). A Lean program (`Main.lean`) serves the page on 127.0.0.1 with core `Std.Http`, or on the address in `HOST`. It keeps one game in memory.
- The Engine is a pure function, `step : Game → Input → Roll (Game × List Report)` in `Rpg/Play.lean`. Dice come from a seeded generator, so the same seed and the same clicks give the same game.
- Each Report says one thing the Engine did, such as a roll or a hit. A roll Report carries each die face, the total, the target number, and the result. The page shows these faces; it never makes up a die.
- The server sends the whole view on each reply: the Scene or Fight, the Character, the map, every Report so far, and the inputs the game offers now. A reload or a second tab shows the same game.
- The page (`web/`) is plain HTML, CSS, and JavaScript, with no build step and nothing loaded from the internet.

## How it works

- The DM writes an Adventure as a Lean file, before play. See `docs/dm-prompt.md`.
- `Rpg/Spec.lean` says what a legal Adventure is, in plain Lean.
- `Rpg/Check.lean` has a checker that lists errors in plain words, and the theorem `check_sound`: if the checker finds no errors, the Adventure is legal by the spec.
- Each shipped Adventure has a theorem that it is legal, for example `lighthouse_legal`. The Lean kernel runs the checker to prove it.
- The Engine (`Rpg/Engine.lean`) rolls all dice during play. No AI runs during play, so the DM has no way to change a roll.
- The Adventure types have no way to say "the Character loses HP". Harm only comes from Fights, which the Engine runs.
- Theorems in `Rpg/Play.lean` protect the Engine from the page, which can send any input:
  - `step_rejects`: if the game does not offer an input, `step` returns the same game and the same dice, with one Report that says the input was refused.
  - `mem_inputs_iff`: the game offers exactly the inputs the rules allow. It joins two theorems: `inputs_allowed` (every input the game offers is allowed) and `inputs_complete` (every allowed input is offered). `AllowedInput` in `Rpg/InputSpec.lean` says which inputs are allowed: `begin` only on the title screen, a Choice only from the current Scene's Choices, a Maneuver only on the Character's turn in a Fight that goes on, and an attack only at a living Creature.
- `make check` runs `lake check`, which replays every proof through the Lean kernel. It fails if any proof uses `sorry` or a new axiom. The library builds every file under `Rpg/`, so a new Adventure is checked even if the game does not load it.
- Lean tricks such as `@[implemented_by]` can make the compiled Adventure differ from the one the theorem is about. Two guards stop this. `make check` fails if a file in `Rpg/Adventures/` or `Rpg/Characters.lean` uses an attribute, `unsafe`, `extern`, a macro, or `set_option`. Before it serves the game, the server runs the checker again on the Adventure it will actually play, and refuses to start if there is an error.
- The DM also draws a Picture for each Scene, as an SVG (Scalable Vector Graphics) file in `web/pictures/`. An SVG can carry code, so there are three guards. The page shows Pictures only through `<img>` tags, which run no scripts. The server sends a CSP (Content Security Policy) header that allows only scripts, styles, and images from the server itself, and no inline script. `make check` runs `scripts/check_pictures.py`, which reads each Picture as XML. It fails on a DOCTYPE or ENTITY, a file that is not well-formed, a script, `<foreignObject>`, `<iframe>`, `<object>`, `<embed>`, or `<a>`, an event handler such as `onload=`, an animation that changes an event handler or a link, any link that does not start with `#`, and CSS that loads from outside. It also fails on any file in `web/pictures/` that is not an SVG file.
- Other websites open in the same browser cannot drive the game. The server refuses (403) every POST that does not say its body is JSON, and every POST whose `Origin` is not the game's own page. A browser must ask first before another site can send JSON, and the server does not agree. A request body over 4 KB gets 413.

## What the spec checks

1. Every Creature is a legal build: attributes 1 to 20, at most 150 points, skills bought correctly, ST high enough for its weapon.
2. Every Success Roll has a modifier from -10 to +10, and the Character can try it: the Character can use the skill, and the effective skill is 3 or more. So both results of the roll can happen in play.
3. Every Scene a Choice leads to exists, and so does the start Scene. No two Scenes share a number.
4. At least one Scene is an Ending.
5. Every Fight has a Creature and can end: the Character can hurt each Creature, or the Creature can hurt the Character. "Can hurt" means an attack skill of 3 or more and a best hit that gets past DR.
6. Every Scene can be reached from the start Scene.

The spec does not say that an Adventure is fair or can be won. A Fight that the Character cannot win, a Fight against many Creatures, or a Scene from which no Ending can be reached is legal. Fairness rules are planned for a later version.

`Rpg/Adventures/Illegal.lean` has seven cheating Adventures. For each, a proof shows the spec rejects it and the checker reports it.

## What is trusted

- The spec (`Rpg/Spec.lean`) and the definitions it uses in `Rpg/Rules.lean` and `Rpg/Adventure.lean`. Read these to know what the theorems mean.
- The Character. Each legality theorem is about one Character, for example `LegalAdventure mara lighthouse`. The same Adventure can fail for another Character. `mara_legal` proves that Mara is a legal build.
- The rules in `Rpg/Rules.lean` were typed in from GURPS Lite by hand. A person must check them against the book.
- The spec for inputs (`Rpg/InputSpec.lean`) and the game types it uses in `Rpg/Game.lean` and `Rpg/Engine.lean`.
- The Engine has no proofs beyond the input theorems. For example, nothing proves that a Fight follows the GURPS rules.
- The server and router code (`Main.lean`), and the Picture check (`scripts/check_pictures.py`), and the view and map code (`Rpg/View.lean`, `Rpg/Map.lean`) have no proofs. Tests check the map rules.
- The page is trusted to draw the Reports as they are. It draws only what the server sends.
- Lean's `Std.Http` server, and the browser.
- Axioms: the theorems use only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Scope of this version (v0)

This is a 1-hour slice of the design. Left out for now: Items and Flags, Quick Contests, Parry, attack modes (each weapon has one), shock, rest, and more than one Character. The only maneuvers are Attack, All-Out Attack, and All-Out Defense, and Creatures always choose Attack. Proofs about the Engine, other than the input theorems, are also left for later.

Deviations from GURPS Lite are in `docs/gurps-deviations.md`. Design rules that are not GURPS rules: the point caps, the -10 to +10 modifier limit, the rule that the Character can try every roll, and natural DR for Creatures at 5 points per level (the full GURPS price; GURPS Lite has no such trait). In turn order, a tie that is left after Basic Speed and DX goes to the Character; GURPS rolls for it.

Design notes: `GLOSSARY.md`, `docs/adr/`.
