# Prompt for the DM (Dungeon Master) agent

Write one new adventure for the game in this repository.

Read `Rpg/RuleSet.lean`, `Rpg/Spec.lean`, `Rpg/Probability/Fairness.lean`,
`Rpg/Probability/Weibull.lean`, and `docs/probability-model.md` first.
`Rpg/Rules.lean` supplies reusable GURPS Lite mechanics, not a selected global
ruleset. `Rpg/Adventures/Lighthouse/` shows narrative authoring;
`Rpg/Adventures/Harbor/` shows a complete certificate.

Create a folder `Rpg/Adventures/<Name>/`, using namespace `Rpg.<Name>`:

1. `Rules.lean`: the adventure's own `rules : RuleSet`. Fields default to GURPS
   Lite mechanics; override them to express this adventure's rules.
2. `Characters.lean`: its player character and creatures. Prove
   `LegalCharacter rules hero` using `checkCharacter_sound`.
3. `Story.lean`: one `Adventure` and its `LegalAdventure rules hero story` proof.
4. `Certification.lean`: prove
   `Probability.isFair Probability.defaultPolicy
     (Probability.adventureGraph rules hero story)`, then construct a
   `Probability.CertifiedAdventure` with `rules`, `hero`, `heroLegal`, `story`,
   `legal`, and `fair`.
5. A public entry point `Rpg/Adventures/<Name>.lean` importing the certification.

Add only the certified value to `Rpg/Catalog.lean`. The terminal uses this
catalog and passes the certified rules to the engine. Do not import another
adventure's cast or use a global player character.

Use `checkCharacter rules hero` and `check rules hero story` for legality errors.
`checkFairnessThrough` checks initial conditions and finite-horizon probabilities;
passing it is not a proof for all times or a normalization proof. The certificate
must cover every time with positive active probability and use the shared Weibull
constants. Preserve HP across fights and derive all encounter odds from the
same rules used by the engine.

Edit this adventure's rules deliberately, then reprove its certificates. Do not
weaken the shared specifications, engine, probability model, or Weibull policy to
make a story pass. Change the story or report why you cannot certify it.
Do not use `sorry`, `axiom`, `native_decide`, or unlimited heartbeats.
Run `make build`, then `make check` on Linux. On macOS, report that the additional
`lake check` replay is unavailable. Uncertified stories may remain authoring
candidates but must not be inserted into the playable catalog.

## Statistical admission option

When explicitly choosing statistical confidence instead of an exact `isFair`
proof, read `docs/statistical-confidence.md`. Supply a `StatisticalCandidate`
with a proved decreasing scene rank, then register it in `statisticalCandidates`.
Only `admitStatistically` can supply the source-bound runtime evidence needed to
enter the menu. Do not relabel exploratory `make audit` output as a certificate.
The Lean confidence theorem is conditional on its binomial sampling model;
state that assumption and the remaining source-to-model proof boundary.
Freeze parameters before a fresh held-out experiment. Do not tune on validation
results and continue to claim the same precommitted error bound.
