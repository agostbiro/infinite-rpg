# Balance and lifetime study

The [report](results/report.html) has charts and tables from 175,000 simulated games, made before the built-in adventure was removed: seven variants of two adventures, nine balance-curve settings, 20,000 lifetime runs per variant, and five balance checks of 1,000 games per variant.
The [plan](plan.json) fixes all seeds and settings.
A different balance curve does not change the game, so all settings use the same games.

## Results

- The default check rejected the unchecked weapon, the too-strong enemies, and the variants with no fights, in all five batches. With the tolerance widened to ±0.30, every variant passed all five.
- In the expanded built-in adventure (now the test adventure, with the same graph), 67.60% of the games with the random model player ended in death. Characters who died made 4.81 Scene choices on average.
- The default check also passed Silver Acorn, where 83.44% of games end in death. The check looks at when deaths happen in the first turns, not at the overall win rate.

The study only explores. It does not replace the balance check, and it does not prove confidence across all the comparisons at once.
The study ran with 1,000 games: "the default check" above is the game's curve, with a tolerance of 20 points.
The game now uses 1,200 games, so `lake exe balance-study` refuses this plan until a new plan is written.
The study code now runs on the test adventure, with five variants; its new results are not made yet.

## Run it

From the repository root, run the study, then make the report:

```sh
python3 scripts/run_balance_study.py
uv run --no-project --with matplotlib==3.11.2 python scripts/report_balance_study.py
```

The study takes about a minute.
The first script runs `lake build`, so do not run it while another `lake` process uses the same checkout.
Without `uv`, install `matplotlib` from [requirements.txt](requirements.txt) and run the second script with `python3`.

## Files

- [plan.json](plan.json): the variants, seeds, and settings.
- [adventures/](adventures): the Silver Acorn. The study builds the test adventure from the Lean code.
- [results/](results): the raw data, the charts, and the report. `metadata.json` holds a hash of each source file that the study used.
