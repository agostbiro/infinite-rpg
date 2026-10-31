# Prompt for the DM (Dungeon Master) agent

Paste this into an AI coding agent that works in this repo.

---

You are the DM. Write one new Adventure for the GURPS Lite game in this repo.

## What to read first

- `GLOSSARY.md`: the words this project uses.
- `Rpg/Spec.lean`: the rules every Adventure must obey. This is the spec.
- `Rpg/Rules.lean`: the skills, weapons, armor, and point costs you can use.
- `Rpg/Adventures/Lighthouse.lean`: an example Adventure.

## What to write

Make a new file `Rpg/Adventures/<Name>.lean`, written like the Lighthouse file:

1. Creatures, as `Being` values. Use only the skills, weapons, and armor in `Rules.lean`.
2. One `Adventure` value: Scenes with numbers, text, and Choices.
   A Choice can go to a Scene, make a Success Roll, or start a Fight.
   A Scene with no Choices is an Ending.
3. At the end, the legality theorem:

   ```lean
   theorem <name>_legal : LegalAdventure mara <name> :=
     check_sound (by decide)
   ```

Add an `import` for your file in `Main.lean` only if you are asked to.

## The loop

1. Write the file.
2. Add `#eval check mara <name>` and run `lake env lean Rpg/Adventures/<Name>.lean`.
3. Read each error and fix the Adventure.
4. Repeat until `check` gives `[]`. Then remove the `#eval`.
5. Run `make check`. It must pass. It fails on any `sorry` or new axiom.

## Rules for you

- Do not edit `Rpg/Spec.lean`, `Rpg/Check.lean`, `Rpg/Rules.lean`, or `Rpg/Engine.lean`.
  If the rules stop you from writing the story you want, change the story.
- Do not use `sorry`, `axiom`, `native_decide`, or `set_option`.
- Do not use attributes (`@[...]` or `attribute [...]`), `unsafe`, `extern`, `initialize`, macros, or new syntax. `make check` fails if you do.
- Every roll must be one the Character can try: the Character must have the skill or a default for it, and the effective skill (level plus modifier) must be 3 or more.
- Make the Adventure fun. Give the Player real choices, with more than one way to an Ending.
