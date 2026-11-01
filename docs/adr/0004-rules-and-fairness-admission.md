---
status: accepted
---

# Each Adventure has its rules, and play needs the balance check

Each Adventure has its own rules value, a `RuleSet` (`Rpg/RuleSet.lean`). The spec, the checker, the Engine, and the balance model all get that same value. Before play, an Adventure must pass the checker and then the balance check (admission): 1,000 seeded games, with exact binomial intervals that must fit a rising Weibull curve (`Rpg/Probability/`). This merges the branch `codex/rpg-fairness-confidence` into the browser game.

## Decisions

- **Keep all 26 fields of `RuleSet`**, the 14 rule functions too, so that a new mechanic can be one field that one Adventure turns on. The cost: every field is part of what "legal" means, so a reviewer must read the defaults once.
- **People own the rules.** `make check-rules` fails if a `Rules.lean` is not `{}`, unless a person puts it on an allow list. That grep is a first guard only. The statement `lighthouse_default_rules` in the person-owned `Comparator/Statements.lean` pins the rules that play and the balance check use, and `make comparator` checks it. Wishes always use `{}`. So the DM still cannot change a roll.
- **The model's Player picks maneuvers at random**, each with chance 1/3. A round can then change the state with no HP loss, so the exact Fight solver solves the states with the same HP together, as a system of at most 3 linear equations.
- **The curve rejects Adventures that are too easy.** Shape 2 (the danger rises), q = 19/20, tolerance 1/5, horizon 5. The values were picked on the screening seed, then the fixed seed was run once.
- **Wishes must pass admission too.** Each of the 3 tries uses a fresh random seed, saved with the Adventure. The false-acceptance bound for a Wish is at most 30%, not 10%.
- **Harbor is removed.** The Lighthouse is the one built-in Adventure. A small safe story stays in the tests (`Rpg/Probability/TestStory.lean`) to show that the hypotheses of `balanced` can be met.

## Considered options

- **RuleSet with data fields only.** A shorter trusted surface, but a mechanic could then only be a switch. Rejected.
- **A model Player that always Attacks.** The old solver would work as it is, but balance would be about a Player who never uses the maneuver menu. Rejected.
- **A floor row** ("at least 10% die in the window") in place of a new curve. Rejected: the curve says when the danger comes, not only how much.

## Consequences

- `StatisticalCandidate.balanced` is a theorem about the test, true for every candidate. The README must not say that an Adventure is "proved balanced".
- The exact model is slow (minutes for a Lighthouse Fight in the interpreter). Only `lake exe agree` and one-off checks run it.
- A DM must write rising danger and paths of 7 or more Choices, or admission fails.
