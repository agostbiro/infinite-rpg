---
status: accepted
---

# The DM can change the rules during play, after the checks pass

Update on `expand_rules`: the start-of-adventure balance decision below is historical. Live changes now use the actual checkpoint and aged Weibull confidence bands; see `Rpg/WorldChange.lean` and `Rpg/Probability/Continuation.lean`.


During play, the Player can ask for a change, such as "I want my character to have a flamethrower now". The DM (Dungeon Master) proposes the change and a counter-rule. The server installs the change only after the checker and the balance check pass. This merges the branch `codex/rpg-live-rule-changes` (commit 4f123d4). For play-time changes, it replaces the "People own the rules" decision of ADR 0004. The rules files and Wishes still follow ADR 0004.

## Decisions

- **The DM can change a target number, but never a die face.** A change can give a weapon, or a combat effect such as +2 to hit, so later rolls get a new target number. The Engine still rolls every die. The checks of a change use their own seeds, so they do not spend the dice of the game in play.
- **A change is data in a small language** (`Rpg/Mechanic.lean`, `Rpg/WorldChange.lean`): equipment, combat effects with triggers, and new or replaced Scenes that are not visited yet. `WorldChange` has its own size limits on a proposal, and the changed Adventure must pass the same checker and the size limits of a Wish. A change cannot write Lean, change the core rules, heal, move the Character, or change a visited Scene. `live_change_core` and `live_change_checkpoint` in `Comparator/Statements.lean` state this.
- **The balance check plays the changed Adventure from its start** (`live_change_from_start`), with 1,000 games and horizon 5, as for a Wish. The game in play keeps its checkpoint: HP, Scene, Fight, and dice.
- **The confidence level is 95% for every admission**, not 90%. `confidenceDelta` goes from 1/10 to 1/20 (`Rpg/Probability/Confidence.lean`). This applies to the Lighthouse, to Wishes, and to saved Adventures too. The bound for a Wish over 3 tries goes from 30% to 15%. The Lighthouse batch (seed 20261103) still passes at 95% (`make validate`, and the table in `docs/statistical-confidence.md`).
- **Retries of a change share one risk budget of 5%.** Validation number `n` uses `confidenceDelta / 2^(n+1)`. `retry_balanced` (`RetryTree.balanced`) proves that the chance to accept an unbalanced change, over any finite series of tries, is at most 5%, under the sampling model at each step. The budget is per server run: a restart gives a new 5%.
- **One change has limits**: at most 6 proposals, 3 validations, and 3 minutes. Each proposal can use up to 3 tries when the API server is busy. A watch task ends the change at 3 minutes and kills its processes, also during a slow call. Then the change fails, and the game is unchanged. Each call can cost money, and each validation uses budget.
- **A change is not saved.** It belongs to the game in memory. "Play again", "← Adventures", and a restart use the original Adventure.
- **Without an API key, the DM can be a signed-in CLI (command-line interface)**: Codex, then Claude Code (`Rpg/GmCli.lean`). Each one runs in an empty temporary folder, with tools and customizations off. For Claude Code, `--safe-mode` turns off `CLAUDE.md` files, hooks, plugins, and MCP servers from every source, `~/.claude` included. `--setting-sources user` loads only the user's `~/.claude/settings.json`. The temporary folder keeps this project's files away. The flags were checked against the help text of Claude Code 2.1.316; no real `--print` call was run. The reply goes through the same checks. Later, these CLI backends were removed: the DM now uses only `ANTHROPIC_API_KEY` (or the recorded replies of `RPG_FAKE_API`).

## What the theorems say, and what they do not say

- `live_change_balanced` (`Admission.balanced`) holds for every proposal. It limits how often the test accepts an unbalanced change. It does not say that a change is balanced. `Admission.intervals_fit` is the fact about one admission: each interval that passed fits its band.
- The 5% for live changes and the 15% for a Wish are separate budgets. For an Adventure from a Wish that gets live changes in one server run, the chance that an unbalanced version was accepted at some point is at most 15% + 5% = 20%.

## Known gaps

These are open. The branch author has them.

- **Deep Scenes get only the legality check** (review finding 2). This gap is stated in the README, in `docs/live-rule-changes.md`, and in the help text of the panel. It is not fixed. The sampled games stop after 6 turns. If a change adds or replaces a Scene that is more than 6 turns from the start, no sampled game reaches it. Its new encounters get the legality check, but not the balance check. Combat rules and equipment apply to every Fight, so the early Fights do test them. A second check from the current checkpoint would close this gap.
- **A counter-rule can be always on in effect** (finding 4). The checker rejects the trigger "always" for a counter-rule. A counter-rule with the trigger `againstFlame`, together with a flamethrower gift, is on in every Fight. The tuning fixture `change-3.sse` does this.
- **Unused continuation fields** (finding 6). `StatisticalCandidate` has `resume` and `elapsed` for a check from a checkpoint. Nothing uses them yet, but they are part of the trusted surface of `balanced`, and they allow combinations with no meaning. Use them for the second check above, or remove them.
- **Equipment is matched by owner name and weapon** (finding 9). A foe with the same name as the Character and the same weapon gets the gift too (`Rpg/RuleSet.lean`).
- **Installation does not check the game again** (finding 11). `applyChange` relies on blocked input to know that the game did not move while the change was checked. This holds now. `preserves_checkpoint` does not state foe HP, turn order, or the round number.

## Considered options

- **Keep ADR 0004: no rule changes during play.** Safer, but no live changes. Rejected: the feature is the point of the branch.
- **Check from the current checkpoint only.** It would test the deep Scenes, but not the changed Adventure as a whole. Not done yet; see the first gap.
- **Fresh 95% tests until one passes.** Simple, but the overall bound is lost. Rejected for the shared budget.

## Consequences

- The trusted surface is larger: the mechanic language (`Rpg/Mechanic.lean`), the `WorldChange` limits and types (`Proposal`, `Prepared`, `Admission`), `RetryTree`, the continuation fields of `StatisticalCandidate`, and the five new statements in `Comparator/Statements.lean` (`live_change_core`, `live_change_checkpoint`, `live_change_from_start`, `live_change_balanced`, `retry_balanced`).
- Wider intervals make a Wish a little harder to pass. A save from another machine can fail the check at 95% and show as a grey card.
- `make comparator` checks 15 statements: the 8 of ADR 0004, the 5 live-change statements, and 2 that came with the shared tactics (`shared_tactical_rules`, `live_change_existing_rule`).
