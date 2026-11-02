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
persistent state, or alter core rules, point budgets, the Weibull curve,
tolerance, or sample count. A proposal has no field for the policy, and `Prepared.keeps_policy`
(`live_change_policy`) proves that a change keeps the game's policy. Unsupported requests receive an explanation. Extending this language requires a
development change and its proofs; runtime does not execute the development skill.

## Checking and installation

1. The server captures the exact checkpoint and blocks other play inputs.
2. `Proposal.prepare` checks limits and obtains Character and Adventure legality proofs
   from the existing sound checkers. Fight legality conservatively includes every extra
   armor and negative hit/damage effect, without relying on positive offensive bonuses.
   This prevents a grant from silently invalidating that check, but can reject playable
   fights whose harmful effects cannot all trigger together.
3. The compiled simulator plays 1,200 games from the adventure beginning on screening seed 1. All Fights use
   the same effects and equipment as play. The rows are compared with the curve of the game's own
   policy (`defaultPolicy`). Failed rows guide revisions to the world's response.
4. A passing proposal is frozen. The server assigns a fresh OS seed and error allowance,
   and plays a separate 1,200-game validation batch against the same curve. Only a source-bound `Admission` value
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
3 fresh validation batches (`maxChangeValidations`), and a 3-minute installation deadline
(`maxChangeMs`) in `Main.lean`. This deadline does not bound certificate computation. With an API key, each proposal can use up to 3 tries when the server is busy
(`callApi`), so one change can send up to 18 requests. The loop of `generateChange` runs over
the fixed list `changeRevisions` (1 to 6), one call for each number, so it cannot run longer
than 6 proposals. Every proposal that is not accepted, parse errors and cut-off replies included,
uses one of the 6. The server checks the proposal and
validation limits after each proposal. At one of them, the change fails with "The Dungeon Master
stopped after N proposals and could not find a balanced version. Your game is unchanged." A watch
task (`watchChange`) enforces the installation deadline: at 3 minutes it marks the change failed
and kills its `curl` processes, as Cancel does, even during a slow provider call. The step then says "The change
reached its time limit of 3 minutes. Your game is unchanged." Acceptance is not guaranteed: some requested mechanics cannot meet the fixed policy.
No failed check becomes a pass and no tolerance or sample count is relaxed. Cancel or failure
leaves play unchanged. The job check prevents a late result from being installed. However,
certificate production runs as pure Lean computation in a dedicated task: cancellation and
the watch do not interrupt it. That task can continue consuming CPU and memory after the
change has failed or been canceled. Starting another request can overlap another producer.

Changes are local to the in-memory playthrough and survive a browser reload. They do not
overwrite saved adventures. Restarting starts the original adventure again.

## What the Player sees

Installation adds one `changeApplied` Report (`Rpg/Report.lean`). The server makes it from the
admitted proposal with `Prepared.note` (`Rpg/WorldChange.lean`): the Player's wish, the summary
and moment, the Character's card and attack level before and after, the requested rules, the
counter-rules as tuned, and the number of changed Scenes. `Prepared.note_rules` proves that the
rules in the note are the rules that the change adds. The view (`changeNoteJson` in
`Rpg/View.lean`) sends the new weapon with its kind (the weapon's JSON name, such as
`broadsword`), its damage and attack, and the weapon it replaces, by Theme Name. Each entry in
`worldRules` has an `origin`: `requested`, `counter`, or `adventure` (`ruleOrigin`).

The page plays the new Report as it plays the Reports of an input (`addsChange` in
`web/change.js`). The 3D tray shows a "World changed" card: "You received: Laser Sabre", its
numbers, what it replaces, and "The world answers" with each counter-rule in plain words. A
rule-only change shows "New rule: ..."; a change of Scenes only shows "The road ahead changed",
with no Scene names. The tray is a live region, so a screen reader reads the change once. A gear
chip next to the HP and the Gear row of the Character panel say "New" until the next input. The
weapon shows in the Player's hand in the 3D view (`web/gear.js` picks a shape from the kind and a
style from words in the name, such as "laser" or "frost"). With reduced motion, nothing animates.
The change panel says "Your change is in play" and tags each rule as "Your change" or "The
world's answer". `tests/live_change_applied.py` checks the Report end to end with a recorded
Laser Sabre change on the built-in Adventure.

## Balance from the beginning and retries

The checker starts at the updated adventure's starting scene, full initial HP, and turn zero.
All new equipment and effects apply throughout these simulated games, including fights
that the player already completed. The check covers the first six scene turns (`H=5`) and
uses the original Weibull bands. Empty late rows and unresolved combat reject the change.

**Deep Scenes are not covered by the sampled balance check.** The sampled games stop after 6 turns. A change
can add or replace Scenes that are not visited yet. If such a Scene is more than 6 turns from
the start, no sampled game reaches it, so its new encounters get legality and combat-termination certification, but not
the sampled balance check. Combat rules and equipment apply to every Fight, so the early Fights do
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
`Prepared.preserves_fight_checkpoint` additionally fixes the whole paused fight record,
including enemy wounds, turn order, round, and maneuvers; only the hero's equipped being changes.
Admission also carries `WellFormed`, the current HP upper bound, `NoShortLoops`, a certificate
for every encounter's combat, and a certificate for the actual paused fight continuation.
These combat certificates establish almost-sure termination under the model's random policy;
they do not turn the six-turn sampled balance check into a balance guarantee for later scenes.

Combat sides and triggers are enums decoded at the JSON boundary. Unknown values are rejected
before constructing a rule. Equipment lookup receives the actual hero/enemy actor explicitly:
an enemy cannot inherit the hero's equipment by sharing its name and weapon. The same lookup
is used by play, the probability model, reports, and the view.

Repeated fresh 95% tests until one passes would lose the overall 95% guarantee. Instead,
validation attempt `n` spends `confidenceDelta / 2^(n+1)`. The server never refunds a spent
allowance, including after cancellation or a later request. With the shared 5% allowance,
the first validation uses 97.5% intervals, the next 98.75%, and so on. All use 1,200 games.
`RetryTree.balanced` proves false-acceptance risk is at most the remaining budget for any finite
adaptive sequence, including subsequent requests after a successful change.

The budget is per server run. `ServerState.changeChecks` counts the validations since the
server started, for all games. A restart starts a new 5% budget. The 5% for live changes and the
25% bound over the five attempts of a Wish (including Retry) are separate. For an Adventure from a Wish that gets live
changes in one server run, the chance that an unbalanced version was accepted at some point is at
most 25% + 5% = 30%.

This assumes the binomial sampling model holds conditional on each history before drawing
the fresh batch. The PRNG's correspondence to ideal sampling remains an accepted assumption.
It is not an all-time gameplay theorem or simultaneous coverage of all intervals. The original
title-screen Wish flow has a separate five-attempt budget, including Retry.

## Turnaround

The DM is asked for a small patch with one or two thematic counter-effects. Equipment and
combat requests default to keeping the existing scenes. Exact interval comparisons stop
refining as soon as their outcome is determined; `lowerMeets_correct` and
`upperMeets_correct` prove equality with the original eight-step endpoint comparisons.
The confidence level, batch sizes, precision, horizon, and rejection rules are unchanged.
On the development Mac, the screening fixture took 14 ms for 1,000 games; exact admission
comparisons fell from 2,960 ms to 625 ms. With 1,200 games on the Linux VM, the same fixture
took about 12 ms to sample and 600 ms to compare (`lake exe change-check --timing`). Two real requests through the Codex CLI (since removed) after the change took
17.1 seconds (weapon) and 19.1 seconds (armor in the Lamp Room), including both batches.
The preceding real request took 156 seconds and needed a second DM proposal. These are
individual measurements from before mandatory whole-adventure combat certification, not
a latency guarantee for the current admission path.

Current whole-adventure certification is a known performance limitation. In the review run,
Lafayette admission had not completed after 120 seconds. Startup performs that admission before
opening the HTTP listener. Saved loads regenerate combat certificates even when a saved verdict
allows the sampled balance check to be skipped; background checking can duplicate that work.

Thirty seconds is an earlier target, not a demonstrated bound for the current checker.
The 3-minute watch prevents late installation and stops provider processes, but it does not
stop pure certificate computation. Cancellation preserves the game, not a CPU or memory budget.
The producer needs bounded or cancellable execution and reusable, independently checked
witnesses; these limits must not be implemented by accepting an unchecked result.

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

`tests/live_change_unsatisfiable.py` starts its own test servers (port 8097 by default) with
recorded replies that can never pass: an unkillable hero, a reply that never parses, a cut-off
reply, a missing counter-rule, a changed gift, an unsupported mechanic, an API refusal, an API
failure, and the time limit. It also tries a Wish whose replies never parse. Each one must end
in a fixed time as failed or refused, say why, and leave the game unchanged. Then the Player
must be able to play on and to try again. Run it after `lake build rpg`, from the repository folder.
The new guarantees are listed in `Comparator/Statements.lean` and proved in its paired
proof file. Isolated proof replay and Comparator require Linux.

## Known gaps

These are open, for the branch author. ADR 0005 has more detail.

- Deep Scenes are outside the sampled balance window (above).
- A counter-rule with the trigger `againstFlame`, together with a flamethrower gift, is on in
  every Fight. The checker rejects only the trigger "always". The tuning fixture does this.
- The statistical model retains `resume` and `elapsed`; admission now accepts only
  `resume = none` and `elapsed = 0`. Conditional balance at a paused checkpoint remains outside its claim.
- `applyChange` does not check again that the game did not move; it relies on blocked input.
  The admitted replacement itself has a checked runtime invariant and preserves the paused fight.
