# No built-in Adventure for now

Superseded: the built-in Adventure is now Lafayette at Barren Hill (`Rpg/Adventures/Lafayette/`).

This ADR changes ADR 0003 and ADR 0004. Those ADRs name The Drowned Lighthouse, the one built-in
Adventure. It is removed. A new built-in default Adventure will take its place later
(`docs/follow-ups.md`).

## The decision

- The Front Page shows the saved Adventures and the Wish form only.
- The server still needs a game in memory while no Adventure is loaded. It holds the test
  Adventure (`homeGame` in `Main.lean`), and it refuses every input until a saved Adventure is
  loaded. A new built-in Adventure takes this place, and gets a card on the Front Page.
- A small test Adventure, The Bandit Camp (`Rpg/Adventures/TestAdventure/`), does the other jobs of
  the Lighthouse. It has the same Scenes, rolls, and Fights as the Lighthouse, with new text and new
  names for the beings, so it passes the checker and the balance check in the same way. It is never
  offered for play.
  - The Comparator theorems `test_adventure_legal`, `test_adventure_reaches_ending`, and
    `test_adventure_default_rules` are about it. They show that the premises of the main theorems
    can be met.
  - `make validate`, `make cheats`, `make agree`, `lake exe change-check`, and the balance study run
    on it.
- The recorded Wish of the test mode (`RPG_FAKE_API`) is removed too: it did not pass the new
  balance check. The test mode stays. The tests that need a recorded Wish say SKIP until one is back.

## Consequences

- Without an API key and with no saved Adventure, there is nothing to play.
- The results in `experiments/results/` were made with the Lighthouse, before this change. The study
  must run again to make new ones.
