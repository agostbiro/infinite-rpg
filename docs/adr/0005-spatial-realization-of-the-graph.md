# The 3D world realizes the existing graph

The player approaches a marked object or character to select an existing input. The browser gets
the permitted inputs from the Lean view. It makes one spatial interaction for each input and
sends that input unchanged when the player reaches its interaction zone.

Movement, camera motion, lighting, and idle time are presentation only. Lean
still decides all outcomes. Combat weapons and shields select the existing maneuvers and
targets. They do not introduce physical damage, range, or real-time enemy turns.

Each scene uses an open, bounded floor. Interaction zones are separated, and scenery does
not block their routes. A larger menu gets a larger floor. Generated adventures
therefore need no new schema or AI-generated navigation geometry.

Three.js 0.180.0 is vendored with its license. The existing Lean server serves
its two modules. No CDN request, JavaScript build, or production npm install is
needed. The CSP is unchanged.

The fairness model and statistical tests remain on the logical graph. In
particular, uniform keys and uniform flattened combat interactions are not substitutes
for the existing uniform choice, then maneuver/target sampling.

The browser is not formally verified. The input gate in Lean remains the
authority. Pure adapter tests and a browser test check the spatial interface.
The complete mathematical contract is in [3d-formalization.md](../3d-formalization.md).

The journal retains the existing transcript, character, map, and accessible input
buttons. A browser without WebGL can use those controls, with an explicit message.

Objects are procedural meshes chosen from cosmetic narrative hints. NPCs recognized
in the prose are decorative, except at explicitly offered conversation choices.
Combat figures and their health come directly from the engine. Unknown prose falls
back to a trail; missing a visual hint cannot remove or create a logical edge.
