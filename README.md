# Verified RPG

A single-player RPG (role-playing game) based on GURPS Lite, played in the browser. The Player types a Wish, such as "I love LOTR, give me an adventure set in the Shire", and an AI DM (Dungeon Master) writes an Adventure and a Character for it. Lean checks each one against the game rules before anyone can play it. The game cannot start an Adventure that has not passed the proved checker: the types do not allow it. Then a fairness check plays the Adventure 1,000 times and rejects it if the Character dies too often, or too rarely, on some turn.

```
make install
make run              # play: opens http://127.0.0.1:8080/ in your browser
ANTHROPIC_API_KEY=sk-... make run   # the same, with Wishes turned on
make run-fake         # test hook: Wishes use recorded replies from tests/fake-api, no key needed
make run SEED=7       # the first game uses dice seed 7, so you can replay it
make run PORT=9000    # use another port
make run HOST=10.211.55.6   # listen on this IPv4 (Internet Protocol version 4) address, for example to play from the host of a VM (virtual machine)
make cheats           # watch the checker catch a cheating DM
make validate         # run the fairness check on The Drowned Lighthouse and print each row
make check            # build, then replay every proof through the Lean kernel
```

## How to play

`make run` builds the game, starts the server, and opens the page. Ctrl-C stops the server.

The Front Page, "Choose an Adventure", shows a card for each Adventure. A card shows the title, the World (where the Adventure takes place), the Character you play, and where the Adventure comes from. Click a card to start playing. The newest Adventures come first, then The Drowned Lighthouse, which is built in.

To get a new Adventure, click "+ New Adventure" and type a Wish (at most 500 characters). You can also give the Character a name (at most 30 characters) and pick she, he, they, or "let the Dungeon Master choose". Then click "Ask the Dungeon Master". The tile shows each step: "The Dungeon Master is writing...", the errors of the checker and the fairness check for each try, "The Dungeon Master is fixing them...". The Dungeon Master gets 3 tries. When an Adventure passes, the tile says "Your Adventure is ready", with "Play it now" and "Later". After 3 failed tries, the tile shows the last errors, and you can click "Try again" or "OK". "Cancel" stops the Dungeon Master. While the Dungeon Master works, the cards are disabled and the server refuses every other input. A reload shows the same steps, because the state lives on the server.

Wishes need an API key for the Claude API in `ANTHROPIC_API_KEY`. Without a key, `make run` still works: the "+ New Adventure" tile says that generation is unavailable, and you can play The Drowned Lighthouse and the saved Adventures.

Each Adventure that passes is saved under `adventures/<id>/`, with its Character, World, Intro, Theme Names, and Pictures. A saved Adventure is checked again, with the fairness check and its saved seed, when the Front Page lists it and when you load it. Its Pictures are checked again on load. A save that fails a check now shows as a grey card with the reason, and you cannot play it.

The story opens with the Intro: a few lines that name the World and say who your Character is. Read the Scene and click a Choice. Some Choices make a Success Roll: the dice tumble, then show the faces the Engine rolled.
In a Fight, the Creatures act, then you click a Maneuver. If you attack and more than one Creature is alive, their cards light up: click the one to attack. "Skip" shows the rest of a turn at once.
The Character panel shows the background, attributes, skills, Gear, and HP. The map shows the Scenes you visited and a "?" for each way you have not taken.
"← Adventures" at the top goes back to the Front Page. If the game is not over, the page asks first, because you lose your progress.
The game ends at an Ending, or when the Character dies, which is not an Ending. "Play again" starts the same Adventure with a new seed. The seed is in the corner.

## How the game runs

- The browser draws, and Lean decides (see `docs/adr/0002-browser-draws-lean-decides.md`). A Lean program (`Main.lean`) serves the page on 127.0.0.1 with core `Std.Http`, or on the address in `HOST`. It keeps one game in memory.
- The Engine is a pure function, `step : Game → Input → Roll (Game × List Report)` in `Rpg/Play.lean`. Dice come from a seeded generator, so the same seed and the same clicks give the same game.
- Each Report says one thing the Engine did, such as a roll or a hit. A roll Report carries each die face, the total, the target number, and the result. The page shows these faces; it never makes up a die.
- The server sends the whole view on each reply: the Scene or Fight, the Character, the map, every Report so far, and the inputs the game offers now. A reload or a second tab shows the same game.
- The page (`web/`) is plain HTML, CSS, and JavaScript, with no build step and nothing loaded from the internet.

## How a Wish becomes a game

1. The server sends the Wish to the Claude API (model `claude-opus-5-5`, effort `medium`) with `curl`, because core Lean has no TLS (Transport Layer Security). The API key goes to `curl` on its standard input, not on the command line. The request asks for JSON that follows a JSON schema (structured outputs), so the reply always reads as JSON. It also sets `fallbacks: "default"`, so the API can retry a refused request on another model. The reply streams as SSE (server-sent events), so a long reply never leaves the connection idle; `rebuildStream` in `Rpg/Prompt.lean` joins the events into the same message that a request without streaming gives, thinking blocks and their signatures included. The system prompt is marked for the prompt cache. If the reply is still a refusal, the page says "The Dungeon Master won't write that one. Try another Wish." The prompts are in `Rpg/Prompt.lean`; the rule tables in them come from `Rpg/Rules.lean`.
2. `Rpg/Live.lean` reads the JSON into a `Draft`: an Adventure with Theme Names, a Character, a background, a World, an Intro, and a palette for the Pictures. The World and the Intro change only what the Player sees. An older save has neither: its card then shows the Wish as the World, and the story opens with the background.
3. Size limits come first: at most 40 Scenes, at most 2,000 characters of text in a Scene, at most 120 characters in a title, a Choice, a name, or a Theme Name, at most 60 in the World, and at most 600 in the Intro. A Draft over a limit is a failed try with a plain error. These limits are not part of the spec.
4. `Draft.toGame` runs `checkCharacter` and `check`, with the default rules (`liveRules`). If either finds an error, the server sends the errors back to the DM in a new turn, with how the Character's points add up, and asks for a fixed version.
5. If both find no errors, `Draft.checked` makes an `AdventureDefinition`, which holds the proofs:
   ```lean
   if hc : checkCharacter liveRules d.hero = [] then
     if ha : check liveRules d.hero d.adventure = [] then
       .ok ⟨liveRules, d.hero, checkCharacter_sound hc, d.adventure, check_sound ha⟩
   ```
   `Game.new` takes an `AdventureDefinition`, and a `Game` keeps both proofs as fields. So no code can make a `Game`, and so no code can play an Adventure, without the proofs. The built-in game uses the theorems `mara_legal` and `lighthouse_legal`.
6. Then `Draft.toGame` runs the fairness check (see below) with a fresh random seed from the operating system, and horizon 5. If a row fails, the DM gets one error for each row that failed, with the numbers, and the try counts as a failed try. If every row passes, the game starts, and the seed is saved with the Adventure.
7. Then the server asks the DM for one Picture per Scene, at most 4 at a time, and checks each one with `scripts/check_pictures.py` before it serves it. A Picture that fails, or is still drawing, shows the plain backdrop. Pictures appear as they finish, and you can begin before they are all done. If you switch to another Adventure, the server stops the drawing. When you load the Adventure again, it draws the Pictures that are still missing. A Picture that the check refused is listed in `refused-pictures.txt` in the save folder and is not drawn again.

## How it works

- The DM writes an Adventure as JSON for a Wish, as above. A coding agent can also write an Adventure as a Lean file, before play, with a theorem that it is legal. See `docs/dm-prompt.md`.
- `Rpg/Spec.lean` says what a legal Adventure is, in plain Lean.
- `Rpg/Check.lean` has a checker that lists errors in plain words, and the theorem `check_sound`: if the checker finds no errors, the Adventure is legal by the spec.
- Each shipped Adventure has a theorem that it is legal, for example `lighthouse_legal`. The Lean kernel runs the checker to prove it.
- The Engine (`Rpg/Engine.lean`) rolls all dice during play. The DM takes no part in play, so it has no way to change a roll. The only AI work that can go on after play starts is drawing Pictures, and a Picture changes only what the Player sees.
- The Adventure types have no way to say "the Character loses HP". Harm only comes from Fights, which the Engine runs.
- Theorems in `Rpg/Play.lean` protect the Engine from the page, which can send any input:
  - `step_rejects`: if the game does not offer an input, `step` returns the same game and the same dice, with one Report that says the input was refused.
  - `mem_inputs_iff`: the game offers exactly the inputs the rules allow. It joins two theorems: `inputs_allowed` (every input the game offers is allowed) and `inputs_complete` (every allowed input is offered). `AllowedInput` in `Rpg/InputSpec.lean` says which inputs are allowed: `begin` only before the first Scene (the `title` phase), a Choice only from the current Scene's Choices, a Maneuver only on the Character's turn in a Fight that goes on, and an attack only at a living Creature.
- The fairness check (`Rpg/Probability/`) runs before play. See "The fairness check" below.
- `make check` runs `lake check`, which replays every proof through the Lean kernel. It fails if any proof uses `sorry` or a new axiom. The library builds every file under `Rpg/`, so a new Adventure is checked even if the game does not load it.
- Lean tricks such as `@[implemented_by]` can make the compiled Adventure differ from the one the theorem is about. Two guards stop this. `make check` fails if a file in `Rpg/Adventures/` uses an attribute, `unsafe`, `extern`, a macro, or `set_option`. Before it serves the game, the server runs the checker and the fairness check again on the Adventure it will actually play, and refuses to start if either fails.
- Each Adventure has its own rules, a `RuleSet` (`Rpg/RuleSet.lean`), and the spec reads "legal" under those rules. People own the rules files. `make check-rules` (part of `make check`) fails if a `Rules.lean` under `Rpg/Adventures/` is not `def rules : RuleSet := {}` (the default rules), unless a person puts its path on `RULES_ALLOW` in the Makefile. It also fails if another Adventure file names `RuleSet` or changes a rules value. A Wish always uses the default rules. The grep is only a first guard: a DM could still write a rules value inline in another file. What pins the rules is `lighthouse_default_rules` in `Comparator/Statements.lean`, which a person owns: it states that the Lighthouse uses `{}` everywhere that play and the fairness check read its rules, and `make comparator` fails if that is not so.
- The DM also draws a Picture for each Scene, as an SVG (Scalable Vector Graphics) file: in `web/pictures/` for the built-in Adventure, and in `adventures/<id>/` for a live one. An SVG can carry code, so there are three guards. The page shows Pictures only through `<img>` tags, which run no scripts. The server sends a CSP (Content Security Policy) header that allows only scripts, styles, and images from the server itself, and no inline script. `make check` runs `scripts/check_pictures.py`, which reads each Picture as XML. It fails on a DOCTYPE or ENTITY, a file that is not well-formed, a script, `<foreignObject>`, `<iframe>`, `<object>`, `<embed>`, or `<a>`, an event handler such as `onload=`, an animation that changes an event handler or a link, any link that does not start with `#`, and CSS that loads from outside. It also fails on any file in `web/pictures/` that is not an SVG file. For a live Adventure, the server runs the same script on each Picture before it serves it, and again when a saved Adventure is loaded. The server serves a live Picture only from `/saved/<id>/<name>.svg`, only for the Adventure in play, only if it passed, and with the same path guards as the other files.
- Other websites open in the same browser cannot drive the game. The server refuses (403) every POST that does not say its body is JSON, and every POST whose `Origin` is not the game's own page. A browser must ask first before another site can send JSON, and the server does not agree. A request body over 4 KB gets 413. A Wish of 500 characters fits.
- Text from the DM is shown only as text. The page never uses `innerHTML`.

## What the spec checks

Each number below is the default of the adventure's `RuleSet`. Every Adventure in this repo uses the defaults.

1. Every Creature is a legal build: attributes 1 to 20, at most 150 points, skills bought correctly, ST high enough for its weapon.
2. Every Success Roll has a modifier from -10 to +10, and the Character can try it: the Character can use the skill, and the effective skill is 3 or more. So both results of the roll can happen in play.
3. Every Scene a Choice leads to exists, and so does the start Scene. No two Scenes share a number.
4. At least one Scene is an Ending.
5. Every Fight has a Creature and can end: the Character can hurt each Creature, or the Creature can hurt the Character. "Can hurt" means an attack skill of 3 or more, and some dice results that hit, get past Dodge, and do injury after DR.
6. Every Scene can be reached from the start Scene.
7. From every Scene, some path of Choices leads to an Ending. The dice do not count here: each Scene that an Outcome can lead to is a step.

The spec does not say that an Adventure is fair or can be won. A Fight that the Character cannot win, or a Fight against many Creatures, is legal. Rule 7 does not say that the Character lives to reach an Ending. The fairness check is a separate step, below.

The Character must be a legal build: attributes 7 to 14, exactly 100 points, skills bought correctly, ST high enough for the weapon, and no natural DR.

`Rpg/Adventures/Lighthouse/NegativeExamples.lean` has eight cheating Adventures. For each, a proof shows the spec rejects it and the checker reports it. Cheat 8 is a maze that only leads back into itself, which breaks rule 7. `Rpg/Adventures/Lighthouse/Story.lean` shows that rule 7 holds for The Drowned Lighthouse, both from `lighthouse_legal` and by hand for one Scene.

## The fairness check

The check plays an Adventure 1,000 times with a seeded random generator (`Rpg/Probability/StatisticalAdmission.lean`). On each turn it picks a Choice at random. In a Fight, the Player picks Attack, All-Out Attack, or All-Out Defense, each with chance 1/3, and then a living target at random. One turn is one Choice, with its whole Fight.

It counts the deaths on each turn, for the first 6 turns (horizon 5): death on turn 1, and death on turn t+2 of the games still going at turn t. For each row, it makes a 90% confidence interval (an exact binomial interval). Each interval must fit in a range around a target curve, a discrete Weibull curve with shape 2, q = 19/20, and a tolerance of 1/5 (`Rpg/Probability/Weibull.lean`). Shape 2 means that the danger rises over the turns. So the first turns can be safe, but from turn 4 on the range has a lower edge above 0: an Adventure where the Character never dies fails. A test in `Rpg/Probability/ConfidenceTests.lean` shows this with a count of zero deaths.

The theorem `StatisticalCandidate.fair` is about the test, not about one Adventure. If the games follow the sampling model (`BinomialSampling`), each interval misses the true chance at most 10% of the time, and the test accepts an Adventure that breaks a range at most 10% of the time. The theorem holds for every Adventure, the cheats too. What admits an Adventure is the run-time check `admitStatistically`, or `admitWithSeed` for a Wish.

The built-in Adventure uses the fixed seed 20261103. The build does not replay this run; the server runs it at start-up, and `make validate` prints it (the counts are in `docs/statistical-confidence.md`). The curve values were picked on a separate screening seed (1), and the fixed seed was then run once. A Wish uses a fresh random seed on each of its 3 tries. So for a Wish the chance to accept an Adventure that breaks a range is at most 30%, not 10%.

The exact model (`Rpg/Probability/Combat.lean` and `Graph.lean`) works out the true chances with the same Engine code as play. `lake exe agree` compares it with the simulator on the Lighthouse Fights. The model solves the states of a Fight that have the same HP together, as a small system of linear equations, because a round can change the Character's maneuver without a hit.

## What is trusted

- The spec (`Rpg/Spec.lean`) and the definitions it uses in `Rpg/Rules.lean`, `Rpg/RuleSet.lean`, and `Rpg/Adventure.lean`. Read these to know what the theorems mean. The `RuleSet` has 26 fields, 14 of them functions. Each default is the rule in `Rpg/Rules.lean`.
- The fairness check. `fair` assumes the binomial sampling model: given the number of games in a row, its deaths follow a binomial law with the model's chance. The seeded generator is treated as fair dice and fair random choices; this is not proved. The model's Player (random Choices, each maneuver at 1/3, random targets) is a choice of this design, not a fact about real Players. The curve and its values are design choices too (see `docs/statistical-confidence.md`). For a Wish the bound is at most 30%, because of the 3 tries.
- For a live Adventure, the compiled `check` and `checkCharacter` must give the same answer as the ones in the proofs. A shipped Adventure has a theorem that the Lean kernel checked; a live one has only the run-time check, with `check_sound` as the reason it is enough.
- The Claude API, `curl`, the prompts, and the JSON decoder (`Rpg/Live.lean`) are not trusted, and do not need to be for legality. Whatever comes back, the checker runs on the `Draft` that the decoder made, and only that `Draft` is played. A wrong decoder can only give the checker a different Adventure.
- The Picture check at run time (`scripts/check_pictures.py`), as for the built-in Pictures.
- Theme Names are display only. The spec and the Engine never look at them, and Reports keep the rule data (the skill of a roll, the weapon of an attack). The view (`Rpg/View.lean`) shows the Theme Name in place of the rule name. A Theme Name can mislead the Player (for example, a broadsword called "Spoon"), but it cannot change a rule.
- The Character. Each legality theorem is about one Character, for example `LegalAdventure rules mara lighthouse`. The same Adventure can fail for another Character. `mara_legal` proves that Mara is a legal build.
- The rules in `Rpg/Rules.lean` were typed in from GURPS Lite by hand. A person must check them against the book.
- The spec for inputs (`Rpg/InputSpec.lean`) and the game types it uses in `Rpg/Game.lean` and `Rpg/Engine.lean`.
- The Engine has no proofs beyond the input theorems. For example, nothing proves that a Fight follows the GURPS rules.
- The server and router code (`Main.lean`), the Picture check (`scripts/check_pictures.py`), the view and map code (`Rpg/View.lean`, `Rpg/Map.lean`), and the live code (`Rpg/Live.lean`, `Rpg/Prompt.lean`) have no proofs. Tests check the map rules, the Theme Names in the view, and the JSON decoder on fixtures.
- The page is trusted to draw the Reports as they are. It draws only what the server sends.
- Lean's `Std.Http` server, and the browser.
- Axioms: the theorems use only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Scope of this version (v0)

This is a 1-hour slice of the design. Left out for now: Items and Flags, Quick Contests, Parry, attack modes (each weapon has one), shock, rest, and more than one Character. The only maneuvers are Attack, All-Out Attack, and All-Out Defense, and Creatures always choose Attack. Proofs about the Engine, other than the input theorems, are also left for later.

The skills are Broadsword, Knife, Brawling, Stealth, Lockpicking, Diplomacy, Survival, Naturalist, Occultism, Riding, Climbing, Swimming, First Aid, Fast-Talk, Staff, and Liquid Projector. The weapons are the broadsword, the large knife, the punch, the quarterstaff, and the flamethrower, which sprays every living Creature on each attack. There are no other ranged attacks.

Deviations from GURPS Lite are in `docs/gurps-deviations.md`. Design rules that are not GURPS rules: the point caps, the -10 to +10 modifier limit, the rule that the Character can try every roll, and natural DR for Creatures at 5 points per level (the full GURPS price; GURPS Lite has no such trait). In turn order, a tie that is left after Basic Speed and DX goes to the Character; GURPS rolls for it.

Design notes: `GLOSSARY.md`, `docs/adr/` (ADR, Architecture Decision Record; ADR 0003 is about live Adventures, and ADR 0004 is about rules and the fairness check), `docs/statistical-confidence.md`, and `docs/probability-model.md`.

## Test hook

`make run-fake` sets `RPG_FAKE_API=tests/fake-api`. The server then reads recorded API replies from that folder and never calls the API. Each reply is a recorded stream of SSE events (`.sse`), read by the same code as a real stream. The first reply fails the checker with 4 errors, the second passes the checker and the fairness check ("The Silver Acorn", in the Shire), and one Picture has a script, so it fails the check and shows the plain backdrop. `tests/fake-api/make_fixtures.py` writes these files.
