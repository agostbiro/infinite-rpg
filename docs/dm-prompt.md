# Prompt for the DM (Dungeon Master) agent

There are two ways the DM writes an Adventure.

- **From a Wish, in the game.** The server sends the prompt in `Rpg/Prompt.lean` to the Claude API. It asks for a PG-13 Adventure of 8 to 15 Scenes and a 100-point Character as JSON. The rule tables in that prompt come from `Rpg/Rules.lean`, and the ranges of the balance check come from `Rpg/Probability/Weibull.lean`. The prompt below is the source for its rules, so keep the two in step.
- **As a Lean file, offline.** Paste the prompt below into an AI coding agent that works in this repo.

---

You are the DM. Write one new Adventure for the GURPS Lite game in this repo.

## What to read first

- `GLOSSARY.md`: the words this project uses.
- `Rpg/Spec.lean`: the rules every Adventure must obey. This is the spec.
- `Rpg/Rules.lean`: the skills, weapons, armor, and point costs you can use.
- `Rpg/RuleSet.lean`: the rules value of an Adventure. You always use the default rules, `{}`.
- `Rpg/Adventures/TestAdventure/`: an example Adventure (the test Adventure), in its own folder.
- `docs/statistical-confidence.md`: the balance check that your Adventure must pass.

## What to write

Make a new folder `Rpg/Adventures/<Name>/`, with namespace `Rpg.<Name>`, written like the test Adventure folder:

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
   You can give Theme Names to skills, weapons, and armor (`themes := { skills := [(.broadsword, "Wand Duelling")] }`).
   The Player sees only the Theme Name. The rules do not change.
   At the end, the legality theorem:

   ```lean
   theorem <name>_legal : LegalAdventure rules <hero> <name> :=
     check_sound (by decide)
   ```

4. `Definition.lean`: `def <name>Definition : AdventureDefinition := ⟨rules, <hero>, <hero>_legal, <name>, <name>_legal⟩`.
5. `Confidence.lean`: `balanceHorizon := 5`, a `StatisticalCandidate` with it, and
   `theorem balanced : Probability.Balanced statisticalCandidate := statisticalCandidate.balanced`.
   Copy the test Adventure file and change the names.
6. `Rpg/Adventures/<Name>.lean`, which imports `Confidence.lean`.

Do not add your Adventure to `Rpg/Catalog.lean` or `Main.lean` unless you are asked to. The server
plays only saved Adventures from Wishes now. A new built-in Adventure also needs a change to
`homeGame` and the Front Page (see `docs/follow-ups.md`).

## The loop

1. Write the file.
2. Add `#eval check rules <hero> <name>` and run `lake env lean Rpg/Adventures/<Name>/Story.lean`.
3. Read each error and fix the Adventure.
4. Repeat until `check` gives `[]`. Then remove the `#eval`.
5. Screen the balance check: add
   `#eval Probability.failedRows 5 (Probability.sampleCounts statisticalCandidate 1 Probability.validationGames) Probability.Confidence.confidenceDelta 0 statisticalCandidate.policy` to
   `Confidence.lean` and run `lake env lean` on it. It uses the screening seed, 1, and prints each row
   that fails. Fix the story until it prints `[]`. Then remove the `#eval`. Do not use the fixed
   validation seed to tune the story.
6. Run `make check`. It must pass. It fails on any `sorry`, a new axiom, a forbidden word,
   or a `Rules.lean` that is not the default.

## Rules for you

- Do not edit `Rpg/Spec.lean`, `Rpg/Check.lean`, `Rpg/Rules.lean`, `Rpg/RuleSet.lean`, `Rpg/Engine.lean`, anything in `Rpg/Probability/`, or any file in `web/`.
  If the rules stop you from writing the story you want, change the story.
- Do not use `sorry`, `axiom`, `native_decide`, or `set_option`.
- Do not use attributes (`@[...]` or `attribute [...]`), `unsafe`, `extern`, `initialize`, macros, or new syntax. `make check` fails if you do.
- Every roll must be one the Character can try: the Character must have the skill or a default for it, and the effective skill (level plus modifier) must be 3 or more.
- From every Scene, some path of Choices must lead to an Ending (spec rule 7). The dice do not count: each Scene that an Outcome can lead to is a step.
- The balance check plays your Adventure 1,200 times with random Choices and random maneuvers, and compares the deaths on each turn with the balance curve. The danger must rise over the turns: the first turns can be safe, but from turn 4 on some Fights must be able to kill the Character, and not too often. Most paths must be at least 7 Choices long, or the later turns have too few games. `screen.lean` prints the range for each turn.
- Make the Adventure fun. Give the Player real choices, with more than one way to an Ending.
