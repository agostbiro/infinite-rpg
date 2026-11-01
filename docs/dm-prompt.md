# Prompt for the DM (Dungeon Master) agent

Write one new adventure for the game in this repository.

Read `Rpg/RuleSet.lean`, `Rpg/Spec.lean`, `Rpg/Probability/Weibull.lean`,
`Rpg/Probability/StatisticalAdmission.lean`, and `docs/statistical-confidence.md`.
`Rpg/Rules.lean` supplies reusable GURPS Lite mechanics. Each adventure selects
its own rules; see `Rpg/Adventures/Lighthouse/` and `Rpg/Adventures/Harbor/`.

Create a folder `Rpg/Adventures/<Name>/`, using namespace `Rpg.<Name>`:

1. `Rules.lean`: the adventure's `rules : RuleSet`.
2. `Characters.lean`: its player character and creatures, with a proof of
   `LegalCharacter rules hero` using `checkCharacter_sound`.
3. `Story.lean`: one `Adventure` and its `LegalAdventure rules hero story` proof.
4. A definition bundling those exact rules, hero, story, and both legality proofs
   in `Probability.AdventureDefinition`.
5. `Confidence.lean` or `Certification.lean`: a positive `fairnessHorizon` chosen
   before validation, a `StatisticalCandidate`, and the specialized theorem
   `fair : Probability.Fair statisticalCandidate := statisticalCandidate.fair`.
6. A public entry point `Rpg/Adventures/<Name>.lean` importing the certification.

Register the candidate in `statisticalCandidates` in `Rpg/Catalog.lean`. The
runtime admits it only after source-bound validation passes every row. An admitted
value carries the `fair` theorem, the counts' provenance, and the acceptance proof.
Do not import another adventure's cast or use a global player character.

For horizon `H`, the finite window checks first-turn death and death at `t+2`
conditional on activity at `t`, for `0 <= t < H`. The `fair` theorem proves
confidence interval coverage and bounds false acceptance of the finite window.
Its IID/binomial sampling model is an accepted assumption. No termination,
decreasing-rank, graph-normalization, or tail proof is required for admission.
If a conditional row has no qualifying observations, it cannot be admitted.

Use the shared Weibull and confidence constants. Preserve combat rules and HP
between fights. Freeze the story, rules, policy, window, and protocol before a
held-out validation experiment. If changes are tuned on validation results,
choose a fresh precommitted holdout; do not search for favorable seeds.

Use `checkCharacter rules hero` and `check rules hero story` for legality errors.
Do not weaken shared specifications to make an adventure pass. Do not use
`sorry`, `axiom`, `native_decide`, or unlimited heartbeats. Exploratory `make audit`
output does not supply admission evidence.

Run `make build` and the confidence tests. Run `make check` on Linux; on macOS,
report that the separate `lake check` replay requires Linux namespaces.
