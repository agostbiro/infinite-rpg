# The 3D world shows the graph of the Adventure

This ADR (architecture decision record) adds to ADR 0002. The page shows the Adventure as a 3D
world, from code by antoine-vinciguerra (branch `RPG_3D`). The Player walks to a marked object or
person to pick a Choice or a Maneuver. Lean still decides every outcome.

## The decision

- The page gets the inputs that the game offers from the Lean view. It makes one 3D object for each
  input (`portalsForView` in `web/spatial.js`). When the Player walks into the object, or presses E
  near it, the page sends that input unchanged.
- If the page cannot make exactly one object for each input, it stops and says so, and the Player
  uses the journal. It never drops a Choice, and it never makes a new one.
- Walking, the camera, the light, and the time the Player waits change nothing in the game. The
  automatic walk to the next place (`web/travel.js`) moves the camera only. It never picks a Choice.
- In a Fight, a sword or a shield picks a Maneuver and a target that the game offers. There is no
  range, no real-time attack, and no damage from the 3D world. The dice come from the Reports, and
  the page shows them over the world.
- While Reports play, the world shows the state at the last Report on screen (`web/playback.js`),
  not the final reply, and offers no input.
- The kind of object (a door, a boat, a ladder) comes from words in the Choice text. It changes
  only what the Player sees. Unknown text gives a path.
- The landscape comes from the world map of the Adventure (`environment` in `adventure.json`,
  `Rpg/Environment.lean`): up to 12 places, paths, props, and one place for each Scene. The DM writes
  it with the Adventure. `WorldEnvironment.errors` checks it at run time with the size limits, before
  the checker. It has no proofs: it changes only what the Player sees. An Adventure with no map gets
  a default map of four places.
- A change during play keeps the map. It must give each new Scene a place on it (`scenePlaces`).
- A saved verdict covers the map, because the map is in the saved text.
- Three.js 0.180.0 is in `web/vendor/`, unchanged, with its MIT license. The Lean server serves it.
  The page loads nothing from the internet, needs no build step, and the CSP (Content Security
  Policy) stays the same.
- Without WebGL 2, the page says so and shows the text version: the story, the Character, and one
  button for each input.

## Considered options

- **Keep the 2D page next to the 3D one.** Two pages to keep in step. Rejected: the 3D page has a
  text version for browsers without WebGL.
- **Real-time combat in 3D.** It would make the browser decide outcomes. Rejected by ADR 0002.

## Consequences

- The browser code has no proofs. The input gate in Lean (`step_rejects`, `mem_inputs_iff`) stays
  the authority: an input that the game does not offer changes nothing.
- `make test-spatial` tests the parts of the page without a browser: one object for each input, the
  walk, the route, and the playback. `make test-browser` plays a Wish in a real browser with the
  recorded replies in `tests/fake-api`.
- The balance check still plays the graph with a random Choice, then a random Maneuver and target.
  The 3D world does not change what it samples.
