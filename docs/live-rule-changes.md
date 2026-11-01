# Changing rules during play

The DM (Dungeon Master) is the AI that writes Adventures. The Player sees the full name. This
page and [ADR 0005](adr/0005-live-rule-changes.md) describe live changes.

The Player can type a free-form request in **Change the world**, during a Scene or on the
Character's turn in a Fight. A flamethrower is one example, not a special command. Other
requests can grant a weapon profile or add supported combat effects, such as armor or a
bonus that activates when wounded or guarding.

The panel is visible during play even when the DM is disconnected. The DM needs
`ANTHROPIC_API_KEY`. Without it, the panel says that the DM is not connected. Generation
errors remain visible and never bypass admission.

The game pauses while the DM works. The DM sends requested effects separately from
counter-rules. Equipment and requested effects are fixed after the first legal proposal;
later revisions adjust the counter-rules and future encounters. Every proposal needs a
named, conditional enemy response, a dramatic moment, and a player decision. Fun is a
design requirement, not a mathematical theorem.

The DM should work to support the player's mechanic: identify its defining behavior and
try combinations of the supported effects, equipment, and future scenes. Unfamiliar names
and themes are not grounds for refusal, and balance failures call for counter-rule revisions.
If the DM says a mechanic is unsupported, the server requests one additional design pass
before declining. It must explain any remaining missing capability and suggest a playable
alternative, without silently substituting a different mechanic or a cosmetic-only effect.

## Shared defaults

New games and generated Wishes inherit the shared tactical meta rules in
`Rpg/Mechanic.lean`. They appear in the live context as existing effects, and the GM must
balance additional requests around them. `Prepared.preserves_existing_rule` proves that
installation retains every existing effect, including the shared defaults and earlier grants.
The combat preview uses the same trigger function as the Engine.

## Scope

`Rpg/Mechanic.lean` defines the supported language:

- Weapon profiles use a supported attack type with an explicit attack level and damage dice.
  These are real values used by the Engine, not just names. A weapon retains its damage
  type, Strength requirement, and single-target or spray behavior.
- Combat rules change hit chance, damage, or armor. Triggers use current HP, maneuvers,
  or equipment. Requested rules may be unconditional; counter-rules must be conditional.
- The DM can replace unvisited scenes or add future scenes and encounters. It cannot rewrite
  visited scenes, remove past choices, move the Character, heal anyone, or revive defeated foes.

The proposal is JSON data. It cannot write Lean, change the dice, invent arbitrary actions or
persistent state, or alter core rules, point budgets, the Weibull curve, tolerance, or sample
count. Unsupported requests receive an explanation. Extending this language requires a
development change and its proofs; runtime does not execute the development skill.

## Checking and installation

1. The server captures the exact checkpoint and blocks other play inputs.
2. `Proposal.prepare` checks limits and obtains Character and Adventure legality proofs
   from the existing sound checkers. Fight legality conservatively includes every extra
   armor and negative hit/damage effect, without relying on positive offensive bonuses.
   This prevents a grant from silently invalidating that check, but can reject playable
   fights whose harmful effects cannot all trigger together.
3. The compiled simulator plays 1,000 games from the adventure beginning on screening seed 1. All Fights use
   the same effects and equipment as play. Failed rows guide revisions to the world's response.
4. A passing proposal is frozen. The server assigns a fresh OS seed and error allowance,
   and plays a separate 1,000-game validation batch. Only a source-bound `Admission` value
   permits installation. Failure returns to revision with a smaller remaining allowance.
5. Installation preserves play RNG, reports, trail, HP, and current scene. A Fight also keeps
   enemy HP, last maneuvers, turn order, and round number. Changes take effect on the next action.

If a legal proposal fails screening, the server first tries bounded numeric adjustments to
positive enemy counter-effects, keeping their names and triggers. This exploratory search
uses only screening seed 1 and checks a six-second budget between variants. It never changes the requested gift
or spends a validation allowance. Descriptions are regenerated with the actual adjusted
numbers. A passing variant is frozen before its fresh validation batch; otherwise the DM
receives the failed rows and revises the proposal.

The DM continues until acceptance, cancellation, an unsupported request, an API failure, or
a limit. One change gets at most 6 proposals (`maxChangeCalls`, the support-review pass included),
3 fresh validation batches (`maxChangeValidations`), and 3 minutes (`maxChangeMs`), in
`Main.lean`. With an API key, each proposal can use up to 3 tries when the server is busy
(`callApi`), so one change can send up to 18 requests. The server checks the proposal and
validation limits after each proposal. At one of them, the change fails with "The Dungeon Master
stopped after N proposals and could not find a balanced version. Your game is unchanged." A watch
task (`watchChange`) enforces the time limit: at 3 minutes it ends the change and kills its
`curl` processes, as Cancel does, even during a slow call. The step then says "The change
reached its time limit of 3 minutes. Your game is unchanged." Acceptance is not guaranteed: some requested mechanics cannot meet the fixed policy.
No failed check becomes a pass and no tolerance or sample count is relaxed. Cancel or failure
leaves play unchanged.

Changes are local to the in-memory playthrough and survive a browser reload. They do not
overwrite saved adventures. Restarting starts the original adventure again.

## Balance from the beginning and retries

The checker starts at the updated adventure's starting scene, full initial HP, and turn zero.
All new equipment and effects apply throughout these simulated games, including fights
that the player already completed. The check covers the first six scene turns (`H=5`) and
uses the original Weibull bands. Empty late rows and unresolved combat reject the change.

**Deep Scenes get only the legality check.** The sampled games stop after 6 turns. A change
can add or replace Scenes that are not visited yet. If such a Scene is more than 6 turns from
the start, no sampled game reaches it, so its new encounters get only the legality check, not
the balance check. Combat rules and equipment apply to every Fight, so the early Fights do
test them. This gap is stated here, in the README, and in the panel. It is not fixed.

This is a property of the revised adventure from its beginning. It is not a claim about the
player's conditional risk at their current wounds or position. Installation still keeps the
actual checkpoint: no replay, healing, reset, or repeated enemy turns occurs in the played game.

`StatisticalCandidate.balancedAt` generalizes `balanced` to the actual error allowance.
`WorldChange.Admission.balanced` (`live_change_balanced`) specializes it to the revised adventure. It
holds for every proposal: it limits how often the test accepts an unbalanced change, and it does not
say that a change is balanced. `intervals_fit` is the fact about one admission: every admitted
interval fits its band. `Prepared.candidate_from_start` proves that admission
uses the whole adventure graph at turn zero. `Prepared.preserves_core` and
`preserves_checkpoint` state the scope and state guarantees.

Repeated fresh 95% tests until one passes would lose the overall 95% guarantee. Instead,
validation attempt `n` spends `confidenceDelta / 2^(n+1)`. The server never refunds a spent
allowance, including after cancellation or a later request. With the shared 5% allowance,
the first validation uses 97.5% intervals, the next 98.75%, and so on. All use 1,000 games.
`RetryTree.balanced` proves false-acceptance risk is at most the remaining budget for any finite
adaptive sequence, including subsequent requests after a successful change.

The budget is per server run. `ServerState.changeChecks` counts the validations since the
server started, for all games. A restart starts a new 5% budget. The 5% for live changes and the
15% bound over the 3 tries of a Wish are separate. For an Adventure from a Wish that gets live
changes in one server run, the chance that an unbalanced version was accepted at some point is at
most 15% + 5% = 20%.

This assumes the binomial sampling model holds conditional on each history before drawing
the fresh batch. The PRNG's correspondence to ideal sampling remains an accepted assumption.
It is not an all-time gameplay theorem or simultaneous coverage of all intervals. The original
title-screen Wish flow still has its separate three-attempt policy.

## Turnaround

The DM is asked for a small patch with one or two thematic counter-effects. Equipment and
combat requests default to keeping the existing scenes. Exact interval comparisons stop
refining as soon as their outcome is determined; `lowerMeets_correct` and
`upperMeets_correct` prove equality with the original eight-step endpoint comparisons.
The confidence level, batch sizes, precision, horizon, and rejection rules are unchanged.
On the development Mac, the screening fixture took 14 ms for 1,000 games; exact admission
comparisons fell from 2,960 ms to 625 ms. Two real requests through the Codex CLI (since removed) after the change took
17.1 seconds (weapon) and 19.1 seconds (armor in the Lamp Room), including both batches.
The preceding real request took 156 seconds and needed a second DM proposal. These are
individual measurements, not a latency guarantee across requests.

Thirty seconds is a target for ordinary changes, not a timeout that permits unchecked rules.
Provider delays and additional revisions can take longer, up to the 3-minute limit. The watch
task stops a slow call at the limit. Cancellation preserves the game.

## Verification

`Rpg/WorldChangeTests.lean` checks grants, non-weapon rules, forbidden changes, triggers,
state preservation, incomplete samples, and resumed play/simulator agreement on 30 seeds.
`lake exe change-check` runs the compiled screening fixture. Its example grants a Stormglass
Flamethrower, adds Scorched Fury to wounded enemies, and gives guarded turns a Cinder Veil.

The HTTP test uses recorded API replies and no paid generation:

```sh
lake build rpg change-check
RPG_FAKE_API=tests/fake-api .lake/build/bin/rpg --port 8087 --seed 7
# In a second terminal, against that disposable session:
python3 tests/live_change_integration.py
# On a fresh test server, test from the Lamp Room:
python3 tests/live_change_integration.py http://127.0.0.1:8087 --late
```

For a test of the time limit, start the fake server with `RPG_CHANGE_LIMIT_MS` (read only
together with `RPG_FAKE_API`), for example 2000. The value must be a whole number of
milliseconds, 1 or more; the server warns about any other value and keeps 3 minutes. The
"TEST MODE" line prints the active limit. A change then ends at that limit, during a recorded reply.

It checks rejection before play, cancellation, blocked inputs, reconsideration of a premature
capability rejection, rejection of a missing counter-rule, actual admission, and preservation
of the game's next dice roll. Generate fixtures into a temporary folder with
`make_fixtures.py FOLDER --tuning` and run the HTTP test with `--late --tuning` to exercise
local counter adjustment followed by fresh admission. `change-check --timing` measures
sampling and exact interval comparison separately; `--tuning` screens a too-strong
counter and verifies that a bounded variant passes without changing the gift.
The new guarantees are listed in `Comparator/Statements.lean` and proved in its paired
proof file. Isolated proof replay and Comparator require Linux.

## Known gaps

These are open, for the branch author. ADR 0005 has more detail.

- Deep Scenes get only the legality check (above).
- A counter-rule with the trigger `againstFlame`, together with a flamethrower gift, is on in
  every Fight. The checker rejects only the trigger "always". The tuning fixture does this.
- `StatisticalCandidate.resume` and `elapsed` are not used, but they are part of the trusted
  surface of `balanced`.
- Equipment is matched by owner name and weapon, so a foe with the Character's name and weapon
  gets the gift too.
- `applyChange` does not check again that the game did not move; it relies on blocked input.
  `preserves_checkpoint` does not state foe HP, turn order, or the round number.
