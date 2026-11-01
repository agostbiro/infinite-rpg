# Balance and lifetime study

The [report](results/report.html) has charts and tables from 175,000 simulated games: seven variants of two adventures, nine balance-curve settings, 20,000 lifetime runs per variant, and five balance checks of 1,000 games per variant.
The [plan](plan.json) fixes all seeds and settings.
A different balance curve does not change the game, so all settings use the same games.

## Results

- The default check rejected the unchecked weapon, the too-strong enemies, and the variants with no fights, in all five batches. With the tolerance widened to ±0.30, every variant passed all five.
- In the new Lighthouse, 67.60% of the games with the random model player ended in death. Characters who died made 4.81 Scene choices on average.
- The default check also passed Silver Acorn, where 83.44% of games end in death. The check looks at when deaths happen in the first turns, not at the overall win rate.

The study only explores. It does not replace the balance check, and it does not prove confidence across all the comparisons at once.
The game still uses its original curve and confidence level.

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
- [adventures/](adventures): the two adventures that the study plays.
- [results/](results): the raw data, the charts, and the report. `metadata.json` holds a hash of each source file that the study used.
