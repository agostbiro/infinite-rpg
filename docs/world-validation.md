# Continuous world validation

Local run: 1 November 2026, macOS, branch `RPG_3D`.

## Previous world implementation (before automatic balancing)

### Checks completed

- Lean build: 76 jobs, successful, no unfinished proof warnings.
- Eighteen JavaScript tests pass: offered-command identity, rejected/missing mappings, combat targets, report-driven health and dice, scene coverage, movement without graph changes, collisions, and path/interaction reachability in desert and forest plans.
- Lean Draft guards cover round trips for all three difficulty profiles and world plans; missing environments, disconnected paths, duplicate place ids, missing/unknown scene ids, unknown props, out-of-bounds props and blocked corridors are rejected.
- API guards reject unsupported difficulty values and preserve Easy as the default for old callers.
- Axiom audit of difficulty validity, ten-choice targets, strict difficulty ordering, existing legality results and statistical interval results finds only `propext`, `Classical.choice`, `Quot.sound`.
- `git diff --check` succeeds.

## Actual Wish pipeline, using local SSE recordings

The API response is parsed by the production decoder and receives the selected profile from the server. The first file has disconnected locations and is rejected. The second file passes Easy admission, saves `difficulty-easy-v1`, and exposes its environment and NPC names through `/api/view`.

Observed Easy timings: 3,012 ms replay delay, 2,864 ms validation, 5,879 ms total. These are **fixture timings**, not Claude API timings.

The same candidate passes Medium with `difficulty-medium-v1` saved and the same environment preserved. It fails Hard's statistical rows. No difficulty check is bypassed for recordings. This also demonstrates why the unchanged 0.2 admission tolerance permits overlap between difficulty classes; survival percentages are target-curve values, not exact measured survival promises.

A separate forest file with different locations, models, NPCs and scene placement passes the same file loader and renders as a forest. No renderer edits are needed to switch between these plans. That file is a local rendering fixture, not a claim of a real model-generated campaign.

## Browser observations

Using the real in-app browser controls:

- The English Wish form presents Easy 50%, Medium 30%, Hard 10%, explicitly labelled survival at ten choices.
- The generation UI displays the disconnected-path error, correction and successful admission.
- The Napoleon campaign starts with its NPC and exactly two engine choices.
- Walking into the conversation changes to Salma's Tent. The world build count stays at one; player coordinates remain approximately (-56.754, 52.712).
- Selecting the next choice changes the objective to Alexandria Harbour, 38 m away. The player stays at the camp and walks along the trail to reach it.
- Walking into the offered combat choice starts the real fight. Attack displays the authoritative dice (3, 4, 4, total 11 in this run), with maneuver controls and combat reports.
- The forest plan shows Pine Camp, its own two-place mini-map and Mira as a character.
- No browser errors or warnings were observed in the inspected sessions.

The full Playwright test is updated for the new world and campaign. Its standalone browser launch was blocked by the macOS execution sandbox; it is not reported as passing. Browser verification above used the available in-app browser.

## Statistical sample and timing limits

The English Napoleon file, with 117 scenes and a minimum 64-choice successful path, keeps its existing `exploration-10-v1` policy. At fixed seed 20261103, 1,000 games pass through 15 choices. There are 474 deaths by choice ten; the 90% death interval is [57/128,129/256], or approximately [44.53%,50.39%].

In one local assembly/inspection run: file assembly including the world was 2.94 ms, statistical validation 6,854 ms, all in-process inspection 7,733 ms, and Python assembly plus subprocess startup and installation 12,443 ms. Load and warm-cache timings vary. In the final browser load, static environment construction took 8.4 ms and the first rendered frame was ready after 67.1 ms. Rendering separately exposes `data-environment-build-ms` and `data-environment-first-frame-ms` on the world element.

No live Claude generation was tested because no API key was configured. Its real latency, retries, model output quality and ability to satisfy a given difficulty remain to be measured with a key. The existing longer 30/60-choice diagnostics are not admission guarantees.

Comparator and `lake check` require their Linux sandbox and remain unexecuted successfully on this macOS environment. This report does not claim end-to-end formal verification of WebGL, collision physics, language or story quality.


## Graph validity and automatic balancing — 1 November 2026

The new theorem names are `equilibrium` and `non-cyclic`. Their complete statements are in
`3d-formalization.md`, alongside the reference to the fairness theorem. They compile in Lean;
axiom audits find only `propext`, `Quot.sound` and `Classical.choice`. The non-cyclic proof uses
only `propext` and `Quot.sound`. Comparator entries include both names; Linux sandbox replay
with `lake comparator` / `lake check` remains unavailable on this macOS host.

The Napoleon source now has no cycles of lengths 1, 2 or 3. Longer optional investigation
loops remain, and the minimum successful main route still requires 64 choices. All eight
places host events, at least one third of event edges change place, and stable event offsets
vary the interaction positions within each clear area. Map markers have readable numbers
with a location legend on hover and in the accessible description.

The tuner checks 15 strength/weapon-skill combinations on a fixed training seed (20261101),
using 256 games per legal combination. It then screens the selected candidate with 1,000
training games. A frozen candidate receives one held-out batch with seed 20261103 for this
reproducible experiment. This held-out seed was not searched. Actual foe ST/knife levels
changed from 14/15 to 16/17 for Medium and 18/17 for Hard; Easy retained 14/15. Hero, edges,
story and environment remain unchanged by tuning.

| Difficulty | Final admission, 15 choices / 1,000 games | Observed survival at 10 | Training + final test |
| --- | --- | ---: | ---: |
| Easy | Pass | 47.1% | 15.986 s |
| Medium | Pass | 30.4% | 16.795 s |
| Hard | Pass | 18.0% | 18.482 s |

These are observed proportions, not the reference targets. In particular, the existing
conditional-row tolerance permits Hard to pass at 18% observed survival although its reference
curve targets 10%. The test and tolerance were not weakened. Counts and exact interval endpoints
are in `reports/balanced-difficulties.json`. Reproducing the batch is not additional evidence.

A production Wish request on a separate local server, using recorded SSE responses, rejected
a disconnected environment, consumed a corrected response, balanced Hard and passed final
admission in 20.287 s (3.015 s fixture delays; 17.267 s checks). No live Claude call was made.
Failures in structural/training checks allow up to six authoring attempts; a failed final
holdout stops the run and cannot silently trigger fresh seed trials.

Verification: full Lean build, 20 JavaScript tests, positive/negative Lean graph examples,
all three difficulty runs, the real Wish route, save/load, and a browser walk to Napoleon
followed by the offered transition to Salma's scene. The static world and player position
persisted across that transition. The user's existing game on port 8093 was kept running.
