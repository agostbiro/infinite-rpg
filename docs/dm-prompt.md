# Prompt for the DM (Dungeon Master) agent

There are two ways the DM writes an Adventure.

- **From a Wish, in the game.** The server sends the prompt in `Rpg/Prompt.lean` to the Claude API. It asks for a PG-13 Adventure of 8 to 15 Scenes and a 100-point Character as JSON. The rule tables in that prompt come from `Rpg/Rules.lean`. The prompt below is the source for its rules, so keep the two in step.
- **As a Lean file, offline.** Paste the prompt below into an AI coding agent that works in this repo.

---

You are the DM. Write one new Adventure for the GURPS Lite game in this repo.

## What to read first

- `GLOSSARY.md`: the words this project uses.
- `Rpg/Spec.lean`: the rules every Adventure must obey. This is the spec.
- `Rpg/Rules.lean`: the skills, weapons, armor, and point costs you can use.
- `Rpg/Adventures/Lighthouse.lean`: an example Adventure.
- `web/pictures/`: the Pictures for the example Adventure.

## What to write

Make a new file `Rpg/Adventures/<Name>.lean`, written like the Lighthouse file:

1. Creatures, as `Being` values. Use only the skills, weapons, and armor in `Rules.lean`.
   There are 15 skills (Broadsword, Knife, Brawling, Stealth, Lockpicking, Diplomacy, Survival,
   Naturalist, Occultism, Riding, Climbing, Swimming, First Aid, Fast-Talk, Staff) and 4 weapons
   (broadsword, large knife, punch, quarterstaff). There are no ranged attacks.
2. One `Adventure` value: Scenes with numbers, text, and Choices.
   A Choice can go to a Scene, make a Success Roll, or start a Fight.
   A Scene with no Choices is an Ending.
   Give each Scene a Picture: `picture := some "<name>"`. The name has only lowercase letters,
   digits, and dashes, for example `"iron-door"`.
   You can give Theme Names to skills, weapons, and armor (`themes := { skills := [(.broadsword, "Wand Duelling")] }`).
   The Player sees only the Theme Name. The rules do not change.
3. At the end, the legality theorem:

   ```lean
   theorem <name>_legal : LegalAdventure mara <name> :=
     check_sound (by decide)
   ```

4. One Picture for each Scene: `web/pictures/<name>.svg`. See "How to draw a Picture" below.

Add an `import` for your file in `Main.lean` only if you are asked to.

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
2. Add `#eval check mara <name>` and run `lake env lean Rpg/Adventures/<Name>.lean`.
3. Read each error and fix the Adventure.
4. Repeat until `check` gives `[]`. Then remove the `#eval`.
5. Draw the Pictures.
6. Run `make check`. It must pass. It fails on any `sorry`, a new axiom, or a forbidden SVG feature.

## Rules for you

- Do not edit `Rpg/Spec.lean`, `Rpg/Check.lean`, `Rpg/Rules.lean`, `Rpg/Engine.lean`, or any file in `web/` other than your Pictures.
  If the rules stop you from writing the story you want, change the story.
- Do not use `sorry`, `axiom`, `native_decide`, or `set_option`.
- Do not use attributes (`@[...]` or `attribute [...]`), `unsafe`, `extern`, `initialize`, macros, or new syntax. `make check` fails if you do.
- Every roll must be one the Character can try: the Character must have the skill or a default for it, and the effective skill (level plus modifier) must be 3 or more.
- From every Scene, some path of Choices must lead to an Ending (spec rule 7). The dice do not count: each Scene that an Outcome can lead to is a step.
- Make the Adventure fun. Give the Player real choices, with more than one way to an Ending.
