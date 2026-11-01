# Wish-generated worlds

Every new Wish follows this pipeline:

1. The player supplies a Wish and `easy`, `medium` or `hard`.
2. Claude returns one JSON adventure: English story, legal character, graph, and `environment`.
3. `Draft.ofJson` decodes it. The validator checks world layout, character legality, graph legality and the absence of event cycles of one, two or three edges.
4. Local balancing tests 15 enemy strength/skill variants with 256 training games each, then checks the selected candidate on 1,000 training games. Structural or training errors go back to Claude for up to six repairs. Once frozen, a candidate receives one independent final batch of 1,000 games through 15 choices. A failed final batch stops admission; the server does not search final seeds for a passing result.
5. The accepted JSON is saved with its fairness profile and simulation seed. Three.js builds the persistent world locally. A generated world needs no additional image or model API requests.

The Napoleon example is authored data in `campaigns/napoleon.json`. The renderer does not contain its map, coordinates or scene-to-place mapping. Any Wish uses the same format and reusable models. NPC costumes may have cosmetic name-based hints; they cannot change commands.

## File format

The full API schema is `Rpg/Prompt.lean:adventureSchema`. Its `environment` field contains:

| Field | Meaning and checked limits |
| --- | --- |
| `theme` | `desert`, `forest`, `coast`, `snow`, `space`, `city` |
| `places` | 2–12 `{id,name,kind,x,z}` records; unique ids; English names requested; coordinates in ±85 m; at least 24 m between centres |
| `paths` | Up to 30 `{fromPlace,toPlace}` records; existing, different endpoints; connected as an undirected network |
| `props` | Up to 80 `{kind,x,z,scale,heading}` records; coordinates in ±100 m; scale 50–200%; heading 0–359° |
| `scenes` | Exactly one `{scene,place,npcs}` record per story scene, including endings; at most four NPC names per scene |

Place kinds: `camp`, `harbour`, `village`, `market`, `ruins`, `temple`, `forest`, `outpost`.
Prop kinds: `pyramid`, `palm`, `tree`, `rock`, `house`, `tent`, `column`, `boat`, `river`.

For campaigns with at least 16 scenes, every place must host events and at least one third of unique event edges must cross between places. Within a place, stable scene-specific offsets vary interaction positions without moving the landscape.

Each scene has at most four choices in this spatial format. Solid props must avoid each location's 10 m interaction area and a 4 m wide corridor along every path. Runtime movement uses conservative collision discs. Rivers are shallow visual water; they introduce no drowning rule. Built-in scenery also avoids those corridors. The world is a 230 × 230 m walking area; its coordinates and scene placements remain stable for the adventure.

Only `view.inputs` supplies commands. A trail is scenery, a graph edge is a scene choice. Walking to another location neither advances the graph nor reveals future interactive choices. Scene transitions relocate the currently offered objects, leaving the player and static landscape in place. Combat buttons expose the same maneuvers and targets as the engine.

The validator checks syntax, references, bounds, connectivity, clearances and graph legality. It does not prove the rendered world correct, understand the prose, or detect every non-English sentence. English is a generation instruction; NPC names and dialogue may still require editorial review.

Older adventures without an environment remain readable and receive a generic connected world. A new difficulty-profile Wish must include an environment.

## Difficulty curves

A turn is one resolved scene choice, including any complete fight. It is not a second, a movement key or a combat round. The uniform player is used only for statistical tests.

For target survival `p` at choice 10 and fixed shape 2:

`S(t) = exp(-(t/λ)²) = p^((t/10)²)`, with `λ = 10 / sqrt(-ln p)`.

Lean evaluates the discrete curve `S(n) = q^(n²)` using rational parameters:

| Difficulty | S(10) target | λ | q |
| --- | ---: | ---: | ---: |
| Easy | 50% | 12.011224 | 993092495 / 1000000000 |
| Medium | 30% | 9.113636 | 988032459 / 1000000000 |
| Hard | 10% | 6.590102 | 977237220 / 1000000000 |

Kernel-checked theorems establish valid parameters, strictly ordered ten-choice survival, and approximation error below one millionth. The selected profile is imposed by the server, supplied to Claude, used by statistical admission, and preserved on save/load and retry.

These are reference curves. The admission test retains its 90% confidence intervals and 0.2 tolerance for the existing conditional-death rows. Passing does **not** prove that an actual adventure has exactly 50%, 30% or 10% survival at ten choices, or establish fairness for an unbounded campaign. Human choices can have different outcomes. The authored Napoleon source retains its `exploration-10-v1` profile; the balancing command produces independently checked versions for the three selected difficulty profiles.

## Run and inspect

Set `ANTHROPIC_API_KEY` in the server's environment, then run `make run`. Never put the key in the Wish JSON or browser. Choose New Adventure and a difficulty. Without a key, saved adventures remain playable.

For a local file:

```sh
lake build inspect-adventure balance-adventure
.lake/build/bin/inspect-adventure campaigns/napoleon.json --horizon 14 --seed 20261103
.lake/build/bin/balance-adventure campaigns/napoleon.json hard work/balanced-hard.json
```

For deterministic testing without API charges, `make run-fake` replays local SSE fixtures through the same decoder, validator and admission test. The first fixture contains a disconnected world and is rejected. The corrected fixture is checked again with the selected difficulty. This is not a measurement of Claude's generation latency.

API integration uses [Anthropic's structured JSON output format](https://platform.claude.com/docs/en/build-with-claude/structured-outputs) and the configured [Claude Opus 5.5 model](https://platform.claude.com/docs/en/models/opus-5-5/overview). No live generation was attempted without a key.


The theorem names are `equilibrium` and `non-cyclic`; see the [formalization](3d-formalization.md#10-theorem-equilibrium-validity-includes-balance). Generation is a bounded repair process, not an existence theorem for arbitrary or contradictory prompts. API failures and a failed independent batch still prevent play.
