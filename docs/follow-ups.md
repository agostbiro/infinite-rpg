# Follow-ups

Work that is still open after the port of the 3D client. Do these in this order.

## 1. Add a new built-in default Adventure

The Lighthouse is removed (ADR 0007). Add a new built-in Adventure in its place.

- It must pass the checker, the short-loop rule (No Short Loops), and the balance check at medium
  difficulty, with a tolerance of ±5 points.
- Give it a card on the Front Page (see `renderGrid` in `web/app.js`), and let the server start it.
  It takes the place of `homeGame` in `Main.lean`.
- Move these from the test Adventure (`Rpg/Adventures/TestAdventure/`) to it:
  - the Comparator example theorems `test_adventure_legal`, `test_adventure_reaches_ending`, and
    `test_adventure_default_rules` (rename them, in `Comparator/` and `comparator.json`)
  - `make validate`, `make cheats`, `make agree`, and `lake exe change-check`
  - the balance study (`BalanceStudy.lean`, `experiments/plan.json`). Run it again, and make new
    results in `experiments/results/`. The results there now come from the Lighthouse.
- Run the balance study again at 1,200 games (`difficultyGames`). `lake exe balance-study` now
  refuses `experiments/plan.json`, because the plan asks for 1,000 games.
- The test Adventure fails medium, so it has an exemption: `policy := Probability.defaultPolicy`
  in `Rpg/Adventures/TestAdventure/Confidence.lean` (the old curve, ±20 points). `homeGame`,
  `make validate`, and `lake exe change-check` use it. The new Adventure gets no exemption.

## 2. Add back the fake-mode Wish

The test mode (`RPG_FAKE_API`) has no recorded Wish now, because the old one failed the new balance
check.

- Record Wish replies (`tests/fake-api/adventure-1.sse` and the next ones) that pass at easy,
  medium, and hard. Each needs a world map. Write them with `tests/fake-api/make_fixtures.py`. Do
  not edit the `.sse` files by hand. The server tries `adventure-<level>-<n>.sse` first, such as
  `adventure-hard-1.sse`, and then `adventure-<n>.sse`.
- Record live-change replies (`change-1.sse` to `change-3.sse`) that pass at medium for the
  Character of that Wish. The replies now are for Mara, with a flamethrower.

## 3. Turn the skipped tests back on

When the recorded Wish is back, these tests run again by themselves. Check that each one passes:

- `tests/live_change_integration.py`, plain, with `--late`, and with `--late --tuning`. It prints
  SKIP now.
- `tests/spatial.browser.spec.js` (`make test-browser`). It is skipped now. Change the Scene names in
  it to the names of the new Wish.
- `make run-fake`: a Wish fails now with "no recorded reply".
