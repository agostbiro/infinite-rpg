# Follow-ups

Work that is still open after the port of the 3D client. Do these in this order.

## 1. Add a new built-in default Adventure

The Lighthouse is removed (ADR 0007). Add a new built-in Adventure in its place.

- It must pass the checker, the short-loop rule (No Short Loops), and the balance check with the
  one balance curve (`defaultPolicy`, ±20 points). It needs no exemption.
- Give it a card on the Front Page (see `renderGrid` in `web/app.js`), and let the server start it.
  It takes the place of `homeGame` in `Main.lean`.
- Move these from the test Adventure (`Rpg/Adventures/TestAdventure/`) to it:
  - the Comparator example theorems `test_adventure_legal`, `test_adventure_reaches_ending`, and
    `test_adventure_default_rules` (rename them, in `Comparator/` and `comparator.json`)
  - `make validate`, `make cheats`, `make agree`, and `lake exe change-check`
  - the balance study (`BalanceStudy.lean`, `experiments/plan.json`). Run it again, and make new
    results in `experiments/results/`. The results there now come from the Lighthouse.
- Run the balance study again at 1,200 games (`validationGames`). `lake exe balance-study` now
  refuses `experiments/plan.json`, because the plan asks for 1,000 games.

## 2. Add back the fake-mode Wish

The test mode (`RPG_FAKE_API`) has no recorded Wish now. The old one was removed in the 3D port,
when the balance check was stricter (±5 points). First check whether the old reply
(`git show 966566d^:tests/fake-api/adventure-1.sse`) passes the current check and the short-loop
rule: then it may only need a world map.

- Record Wish replies (`tests/fake-api/adventure-1.sse` and the next ones) that pass the balance
  check. Record a world map reply for each too (`tests/fake-api/map-1.sse`, `map-2.sse`): the server asks for the map after the Wish passes. Write them with `tests/fake-api/make_fixtures.py`. Do
  not edit the `.sse` files by hand.
- Record live-change replies (`change-1.sse` to `change-3.sse`) that pass the balance check for the
  Character of that Wish. The replies now are for Mara, with a flamethrower.

## 3. Turn the skipped tests back on

When the recorded Wish is back, these tests run again by themselves. Check that each one passes:

- `tests/live_change_integration.py`, plain, with `--late`, and with `--late --tuning`. It prints
  SKIP now.
- `tests/spatial.browser.spec.js` (`make test-browser`). It is skipped now. Change the Scene names in
  it to the names of the new Wish.
- `make run-fake`: a Wish fails now with "no recorded reply".
