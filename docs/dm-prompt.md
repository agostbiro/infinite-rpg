# Prompt for the DM (Dungeon Master) agent

There are two ways the DM writes an Adventure.

- **From a Wish, in the game.** The server sends the prompt in `Rpg/Prompt.lean` to the Claude API. It asks for a PG-13 campaign of 60 to 100 Scenes, with at least 40 Choices on each successful path, a 100-point Character, and a persistent `environment` as JSON, all in English. The selected Easy / Medium / Hard difficulty selects the Weibull reference curve. The environment and its checked limits are described in `docs/wish-worlds.md`. The rule tables in that prompt come from `Rpg/Rules.lean`, and the ranges of the fairness check come from `Rpg/Probability/Weibull.lean`. The prompt below is the source for its rules, so keep the two in step.
- **As a Lean file, offline.** Paste the prompt below into an AI coding agent that works in this repo.

---

You are the DM. Write one new Adventure for the GURPS Lite game in this repo.

## What to read first

- `GLOSSARY.md`: the words this project uses.
- `Rpg/Spec.lean`: the rules every Adventure must obey. This is the spec.
- `Rpg/Rules.lean`: the skills, weapons, armor, and point costs you can use.
- `Rpg/RuleSet.lean`: the rules value of an Adventure. You always use the default rules, `{}`.
- `Rpg/Adventures/Lighthouse/`: an example Adventure, in its own folder.
- `docs/statistical-confidence.md`: the fairness check that your Adventure must pass.
- `web/pictures/`: the Pictures for the example Adventure.

## What to write

Make a new folder `Rpg/Adventures/<Name>/`, with namespace `Rpg.<Name>`, written like the Lighthouse folder:

1. `Rules.lean`: exactly `def rules : RuleSet := {}`, in your namespace. People own the rules.
   `make check` fails if this file says anything else.
2. `Characters.lean`: the Character and the Creatures, as `Being` values, and the theorem
   `<hero>_legal : LegalCharacter rules <hero> := checkCharacter_sound (by decide)`.
   Use only the skills, weapons, and armor in `Rpg/Rules.lean`.
   There are 16 skills (Broadsword, Knife, Brawling, Stealth, Lockpicking, Diplomacy, Survival,
   Naturalist, Occultism, Riding, Climbing, Swimming, First Aid, Fast-Talk, Staff, Liquid Projector)
   and 5 weapons (broadsword, large knife, punch, quarterstaff, flamethrower). The flamethrower
   sprays: each attack hits at every living Creature. There are no other ranged attacks.
3. `Story.lean`: one `Adventure` value: Scenes with numbers, text, and Choices.
   A Choice can go to a Scene, make a Success Roll, or start a Fight.
   A Scene with no Choices is an Ending.
   Give each Scene a Picture: `picture := some "<name>"`. The name has only lowercase letters,
   digits, and dashes, for example `"iron-door"`.
   You can give Theme Names to skills, weapons, and armor (`themes := { skills := [(.broadsword, "Wand Duelling")] }`).
   The Player sees only the Theme Name. The rules do not change.
   At the end, the legality theorem:

   ```lean
   theorem <name>_legal : LegalAdventure rules <hero> <name> :=
     check_sound (by decide)
   ```

4. `Definition.lean`: `def <name>Definition : AdventureDefinition := ⟨rules, <hero>, <hero>_legal, <name>, <name>_legal⟩`.
5. `Confidence.lean`: `fairnessHorizon := 5`, a `StatisticalCandidate` with it, and
   `theorem fair : Probability.Fair statisticalCandidate := statisticalCandidate.fair`.
   Copy the Lighthouse file and change the names.
6. `Rpg/Adventures/<Name>.lean`, which imports `Confidence.lean`.
7. One Picture for each Scene: `web/pictures/<name>.svg`. See "How to draw a Picture" below.

Do not add your Adventure to `Rpg/Catalog.lean` or `Main.lean` unless you are asked to. The server
plays only the Lighthouse and Wishes, so a new built-in Adventure also needs a change to `builtinGame`.

## How to draw a Picture

A Picture is the wide window at the top of a Scene. It changes only what the Player sees.
The spec and the checker do not look at it. If a Picture file is missing, the page shows a plain backdrop.

- Size: `viewBox="0 0 1200 400"`, with `width="1200" height="400"`. Keep the main shapes in the middle
  800 by 300, because a narrow window can cut the edges.
- Style: simple, flat shapes. Polygons, rectangles, circles, and paths. A gradient is fine for a glow.
  Silhouettes, not faces.
- No text in the drawing.
- Palette. Each Adventure has its own palette of 8 to 14 colors that fit its world. The DM picks it
  (for a live Adventure, in the `palette` field of the JSON), and every Picture of the Adventure uses
  only those colors. The palette of The Drowned Lighthouse (night, a dark sea, and lamp light) is:
  - Sky: `#0b1220`, `#121c2e`, `#1b2a40`
  - Sea: `#0d1a26`, `#10243a`, `#163049`, foam `#2c4a66`
  - Rock and shadow: `#070b12`, `#0a0f16`, `#121821`
  - Stone and iron: `#1e2733`, `#2a3544`
  - Lamp light: `#f2b35b`, `#ffd98a`, ember `#c47a2c`, dawn `#3f4a66`
  - Danger: `#8c2f2f`; wood `#2a2116`; steel `#9fb6d0`; paper `#efe4c8`, `#e9e1cf`
  - Rain: `#3a4f6b`
- Forbidden, because an SVG can carry code: `<script>`, any `on...=` attribute (such as `onload=`),
  `<foreignObject>`, and any `href` or `xlink:href` to `http:`, `https:`, `//`, `data:`, or `javascript:`.
  `make check` fails if a file in `web/pictures/` uses one. A gradient or pattern used as
  `fill="url(#name)"` is fine.

## The loop

1. Write the file.
2. Add `#eval check rules <hero> <name>` and run `lake env lean Rpg/Adventures/<Name>/Story.lean`.
3. Read each error and fix the Adventure.
4. Repeat until `check` gives `[]`. Then remove the `#eval`.
5. Screen the fairness check: add
   `#eval Probability.failedRows 5 (Probability.sampleCounts statisticalCandidate 1 1000)` to
   `Confidence.lean` and run `lake env lean` on it. It uses the screening seed, 1, and prints each row
   that fails. Fix the story until it prints `[]`. Then remove the `#eval`. Do not use the fixed
   validation seed to tune the story.
6. Draw the Pictures.
7. Run `make check`. It must pass. It fails on any `sorry`, a new axiom, a forbidden word,
   a `Rules.lean` that is not the default, or a forbidden SVG feature.

## Rules for you

- Do not edit `Rpg/Spec.lean`, `Rpg/Check.lean`, `Rpg/Rules.lean`, `Rpg/RuleSet.lean`, `Rpg/Engine.lean`, anything in `Rpg/Probability/`, or any file in `web/` other than your Pictures.
  If the rules stop you from writing the story you want, change the story.
- Do not use `sorry`, `axiom`, `native_decide`, or `set_option`.
- Do not use attributes (`@[...]` or `attribute [...]`), `unsafe`, `extern`, `initialize`, macros, or new syntax. `make check` fails if you do.
- Every roll must be one the Character can try: the Character must have the skill or a default for it, and the effective skill (level plus modifier) must be 3 or more.
- From every Scene, some path of Choices must lead to an Ending (spec rule 7). The dice do not count: each Scene that an Outcome can lead to is a step.
- The fairness check plays your Adventure 1,000 times with random Choices and random maneuvers. The danger must rise over the turns: the first turns can be safe, but from turn 4 on some Fights must be able to kill the Character, and not too often. Most paths must be at least 7 Choices long, or the later turns have too few games. `screen.lean` prints the range for each turn.
- Make the Adventure fun. Give the Player real choices, with more than one way to an Ending.
