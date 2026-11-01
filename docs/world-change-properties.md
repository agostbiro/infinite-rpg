# Required properties of expanded World changes

Status: specification for `expand_rules`, based on `main` at `f3e8af6`. These are requirements
for the extension. They are not claims that the current server already implements it. The
current behavior and proofs are described in [live rule changes](live-rule-changes.md).
The DM (Dungeon Master) is the GM referred to in the feature request.

## Scope and model

During play, the Player can request new general rules for the Adventure. A request can change
the 3D environment, the available Choices and their outcomes, or both. These are independent
permissions, not exclusive modes. A rule must have an executable meaning in the supported
rule language; a description alone does not implement it.

The DM proposes the requested change and any adjustments needed to keep the Adventure balanced.
It may add Scenes and encounters, revise future behavior of existing Scenes, and add or remove
Choices, including Choices in the current Scene. It may also change places, paths, props and
Scene placements. All parts form one proposed revision.

Use the following notation:

- `G`: the directed game graph. Its vertices are Scene IDs. A Choice has an input identity and
  an Outcome. Each possible destination of that Outcome contributes an edge. A roll can have
  two destinations, so a Choice is not always one edge.
- `R`: the executable Adventure rules and Character definition used by the Engine and simulator.
- `P`: the fixed balance policy and sampling protocol, including the uniform test Player.
- `W`: the 3D places, paths, scenery and interaction layout.
- `m`: the assignment of each Scene to a place in `W`.
- `k`: the play checkpoint, including the current Scene, wounds, Fight state, history and play RNG.
- `v`: the revision of this combined game and world. Revision checks below are new requirements.

A proposal changes `(G, R, W, m)` to `(G', R', W', m')`. The checkpoint continues under the
revised definition after acceptance. A world path is a walking route, not a game edge. Several
Scenes may share a place; matching the two graphs does not require a graph isomorphism.

## 1. The requested rule survives balancing

**`requestPreserved`.** The final proposal implements the Player's requested behavior. The DM
separates that behavior from its balancing adjustments. Revisions may change the adjustments
or add Scenes, but cannot remove the requested rule, restore an explicitly removed Choice, or
replace a requested gameplay effect with a visual effect just to pass a check.

Record the requested effects, Choice edits and spatial constraints separately from the DM's
adjustments, so their preservation can be checked. Whether that supported description faithfully
expresses an unrestricted natural-language request is a separate interpretation task.

Previously accepted rules remain unless the Player explicitly requests their revision. A pure
environment request needs no new combat counter-rule. If a faithful, supported proposal cannot
pass the checks, report that outcome and keep the current game. Acceptance for every possible
natural-language request is not an assumed theorem.

## 2. Core rules, policy and checkpoint are preserved

**`coreAndPolicyPreserved`.** The DM cannot change the Engine's core rules, dice, difficulty,
Weibull parameters, tolerance, test Player, horizon or sample count to obtain acceptance. The
revised rules used in play must be the same rules used by the simulator.

**`checkpointPreserved`.** Installing a change consumes no game action or play RNG value. It
preserves the current Scene ID, HP, completed decisions, Reports and elapsed game turns. In a
Fight it also preserves defeated foes, surviving foes' HP, turn order, maneuvers and round
number. Requested equipment or effects can change as specified, without healing or replaying
a turn. An Outcome already being resolved must finish under its captured revision, or the
change must wait for a safe boundary.

Existing Reports remain an unchanged history prefix. A new Report may describe the accepted
change without claiming that a game action or die roll occurred.

Changing a Choice affects its future use. It cannot rewrite the recorded result of an earlier
use, even if that Choice was taken in a visited Scene. Historical records retain their original
revision and meaning. The current Scene must still exist and admit a valid continuation.

Changing geometry may move the camera to a checked, clear arrival point for the same logical
Scene. This is spatial repositioning only; it cannot select an input or advance the game.

## 3. The complete revised game graph is legal

**`graphValid`.** Check the whole resulting Adventure under `R'`, not just the submitted patch:

- Scene IDs are unique and every Outcome destination exists.
- Every Scene is reachable from the start and has a graph path to an Ending, as required by
  `LegalAdventure`. The current checkpoint remains valid under the revised definition.
- Character, Choices and encounters satisfy the existing legality and size checks.
- Every nonempty closed path has at least four edges. Check every Outcome branch, including
  unlikely or zero-probability branches. `A → A`, `A → B → A` and `A → B → C → A` are rejected.

The short-loop property is `Adventure.noShortLoops` on this version of `main`. Removing an edge
can disconnect a Scene or remove its route to an Ending; the DM must repair that structure while
honoring the request. Adding a Scene also requires a valid placement and reachable interactions.

## 4. The revised gameplay passes balance admission

**`balanceAccepted`.** Every gameplay change must pass the existing admission method on the
complete revised candidate, with the game's fixed policy:

1. Use screening simulations to revise the proposed rules and graph.
2. Freeze the executable candidate before drawing its fresh validation batch.
3. Record counts from that candidate's actual Engine simulations. All required observations
   must be complete, and every confidence interval must fit its policy band.
4. Bind the Admission to the candidate, seed, policy and error allowance that produced it.
   Installation uses that same candidate. Changing it invalidates the old Admission.
5. Charge each fresh validation to the existing retry budget, including after a failed or
   cancelled attempt. Do not reset the budget or repeatedly sample until a proposal passes.

Adding or removing a Choice changes the uniform test Player's distribution: each currently
available Choice has probability `1 / number of available Choices`. Even if retained Outcomes
are unchanged, their old balance measurements cannot authorize the new graph.

`Admission.balanced` and `StatisticalCandidate.balancedAt` prove the test's statistical guarantee
under its sampling assumptions. They do not assert that this particular candidate passed.
An actual `Admission`, its `provenance` and `accepted` fields, and `Admission.intervals_fit` are
required to establish acceptance. Keep that distinction in the DM instructions and UI.

### Scope of the statistical claim

Live changes on `expand_rules` use 1,200 games from the actual revised checkpoint, over the next
six events (`liveHorizon = 5`). The original age is retained and the target is conditional Weibull
survival `S(t+u)/S(t)`. Admission requires every confidence interval to lie within five percentage
points of its target. The original retry allowances are retained. Walking and camera time are
not Scene events. New Wish admission retains its separate existing protocol.

Lean proves checkpoint binding, the reference ratio, interval containment, and the false-acceptance
bound under the sampling assumptions. A pass covers this finite window for the uniform test
Player, not every Scene or every human strategy. A Scene beyond the window still has no
statistical coverage. General persistent-rule and 3D correspondence requirements below remain
extension requirements.

## 5. An environment-only change preserves gameplay

**`visualChangePreservesPlay`.** For a change declared to affect only `W` and `m`, the executable
game graph, rules, available inputs, Outcome distributions and logical checkpoint are unchanged.
For any same legal input sequence and play RNG state, both versions produce the same logical
states, dice and game Reports. Only their spatial presentation may differ.

This must follow from equality of the executable game data or a proved equivalence, not a flag
or assertion supplied by the DM. Separately, `worldMatchesGame` rejects a wall that makes a Choice
inaccessible, including when the executable game data is unchanged.

Existing balance evidence may be reused only when it is still valid for this identical
candidate and protocol. Otherwise normal admission is required. Rechecking the environment is
always required. This avoids spending fresh statistical budget on a proved visual-only change.

## 6. The revised 3D world realizes exactly the revised game

**`worldMatchesGame`.** Verify all of the following for `(G', R', W', m')`:

1. **Complete placement.** Every Scene in `G'` has exactly one valid place in `W'`. There are no
   entries for nonexistent Scenes or places. New Scenes are included. An implicit default map
   must be checked as the actual resulting map; absence of a map is not evidence of consistency.
2. **Exactly the offered inputs.** For each playable state, the enabled 3D interaction objects
   correspond one-to-one with the inputs the Engine offers in that state. Added Choices appear,
   removed Choices disappear, and no duplicate or invented input is enabled. Noninteractive
   scenery and NPCs add no game edge. Terminal states offer no gameplay input.
3. **Same outcomes.** Interacting sends that exact input to the Engine. The Engine alone resolves
   rolls, Fights and destinations. A visual object cannot choose the favorable branch of a roll
   or lead to a destination different from its revised Outcome.
4. **Physical access.** Every offered interaction is reachable from the Scene's safe arrival
   point under the same collision and contact rules used by the page, without first activating
   another Choice. Every possible destination has a safe arrival point and a usable transfer
   route from the source area; a route may have zero length when both Scenes share a place.
   Check paths, obstacles, shifted event anchors and interaction clearance together.
5. **Movement preserves logical state.** Walking that activates no interaction, waiting, camera
   changes and automatic travel leave the game state and play RNG unchanged. Crossing an active
   interaction sends one offered input. After erasing ordinary movement, a 3D play trace must be
   a legal Engine trace of the same revision. Every offered input must also be realizable in 3D.

Thus the navigation graph may have different vertices and paths from `G'`. What must agree is
the set of possible decisions and their Engine outcomes, with physical access to each decision.
Check the spatial obligations with geometry checks and adapter tests tied to the actual page's
layout and collision rules. The balance simulator continues to use the game graph. No
probabilistic verification of 3D physics is required.

## 7. Installation is atomic and uses the checked revision

**`revisionInstalledAtomically`.** Pause gameplay, prepare the game and map, complete their
checks, then install the graph, rules, placements and environment as one revision. The map can
be generated in a separate API call, but the result cannot expose half of a combined change.

Check the live checkpoint and source revision again before installation. Every interaction
request carries its revision. Reject an old request without consuming play RNG, even if its
Choice index now names a different valid Choice. An input being legal in the new graph alone
does not make an old click valid.

The page rebuilds affected objects, NPCs, collision data, map markers and travel routes from the
accepted revision, including when the Scene ID stays the same. Disable old interactions before
enabling new ones. A rendering or mapping failure must not leave stale objects active or be
reported as a successful 3D update.

Failure, cancellation or timeout leaves the playable game and environment at their prior
revision. Validation budget already spent remains spent. No partial proposal is installed.

## Combined admission rule

For proposed revision `X'` of `X`, require:

```text
AcceptChange(X, X') :=
  requestPreserved(X, X')
  AND coreAndPolicyPreserved(X, X')
  AND checkpointPreserved(X, X')
  AND graphValid(X')
  AND worldMatchesGame(X')
  AND (
    gameplayChanged(X, X') AND balanceAccepted(X')
    OR
    executableGameUnchanged(X, X') AND visualChangePreservesPlay(X, X')
      AND validBalanceEvidenceFor(X')
  )
```

Installation must additionally satisfy `revisionInstalledAtomically`. The 3D obligations apply
in both branches, including to a gameplay-only request whose map needs updating to match it.
These names are specification labels, not declarations of completed Lean theorems.

## Implementation obligations and acceptance cases

The extension must replace the current restrictions that keep the map fixed and forbid all
patches to protected Scenes. Keep immutable history rather than freezing every future Choice
of a previously visited Scene. Extend the proposal schema and DM prompt together with their
checkers; prompting the DM to use unsupported fields is not an implementation.

| Case | Required result |
| --- | --- |
| Change the desert to a forest without changing gameplay | Preserve Engine traces; check the new map and every interaction. |
| Remove a Choice from the current Scene | Remove its interaction; reject an old click; recheck graph legality and balance. |
| Add a Scene and an Outcome leading to it | Require a placement, transfer route, valid interactions, legality and balance admission. |
| Change geometry and add a general rule in one request | Check and install both as one revision. |
| Reorder Choices while keeping the same Scene ID | Regenerate interactions and reject requests carrying the old revision. |
| Add a prop that blocks the only access to a Choice | Reject the layout even when the game graph passes its checks. |
| Introduce `A → B → C → A` through any Outcome branch | Reject the graph before admission. |
| Remove the sole route to an Ending or disconnect a Scene | Reject or repair the complete graph without restoring a forbidden Choice. |
| Mutate the candidate after its balance test, or use another candidate's counts | Reject the mismatched evidence. |
| Fail the map check after the gameplay check passed | Keep the prior playable revision; install neither half. |
| Add danger only beyond the sampled window | Do not claim that this new danger was statistically checked. |

Current building blocks are `Proposal.prepare`, `Adventure.noShortLoops`, `Prepared.keeps_policy`,
the existing checkpoint proofs, `Admission` and `RetryTree.balanced`. `WorldEnvironment.errors`
and the spatial tests already check parts of the 3D requirements. They do not yet prove the full
contract above. Map editing, current-Scene Choice editing, complete checkpoint/history coverage,
revision-tagged input rejection and atomic end-to-end refresh remain implementation obligations.
