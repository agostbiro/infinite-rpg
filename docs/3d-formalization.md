# Spatial realization of the existing graph

## 1. Logical game

Let `S` be the logical states. At state `s`, `A(s)` is the finite set of offered commands, and `K(s,a,·)` is the distribution of consequences determined by the engine.

The existing `Adventure`, `Scene`, `Choice` and `Outcome` define the graph. `Game.inputs` exposes valid commands. `step : Game → Input → Roll (Game × List Report)` resolves one command using the existing rules and dice. A player's decision and the machine's random outcome are separate.

## 2. Persistent spatial plan

An adventure file supplies `E = (L,P,D,m,N)`:

- `L`: named places with fixed horizontal coordinates and a supported visual kind.
- `P`: undirected visible paths connecting all places.
- `D`: decorative props with positions, orientations and scales.
- `m`: a total mapping from every story scene to exactly one place.
- `N`: the NPC names present in each scene.

The map is a bounded part of `R³`, navigated on its horizontal surface. It is shared by the whole adventure. The plan contains no commands or probabilistic outcomes. A physical path in `P` is not an extra edge in the story graph.

Claude supplies `E` in the same JSON response as the graph. The server checks references, size bounds, connectivity and clearances before accepting the file. The renderer uses a finite library of procedural models. The Napoleon environment is one instance of this format.

## 3. Projection and continuous movement

A presented state is `w = (s,E,y)`, where `y` contains position, camera orientation and animation data. Define `α(w) = s`.

Movement, waiting and looking produce `(s,E,y) → (s,E,y')`, so `α` is unchanged. They send no game command, consume no logical dice and cause no damage.

Physical time drives movement and animation. It is sampled each frame with a bounded step; collision movement is subdivided, and interaction entry is checked along the movement segment. No infinitesimal number field is used.

The time of the next command may be infinite if the player keeps wandering. The model deliberately does not turn that waiting time into an implicit probabilistic event.

## 4. Exact command representation

For the current view `v`, construct the interaction set `I(v)` at `m(scene(v))`. Each object or conversational NPC `p` carries a command `β(p)` copied unchanged from `view.inputs`.

The required contract is:

`{ β(p) : p ∈ I(v) } = A(α(w))`.

The adapter creates one interaction for each offered command. It refuses an incomplete or duplicate mapping. Labels, NPCs and scenery never infer a destination or add a command. A decorative NPC cannot be spoken to unless the current graph offers a corresponding choice.

An appearance function chooses a table, chest, ladder, boat, telescope, trail, person, weapon or shield. It does not change `β`. Combat controls represent the offered maneuver/target pairs, including defense.

## 5. Navigation

The intended accessibility contract is that every current command can be selected without first selecting another command. No path may add a command.

New world files have at most four scene choices. Their interaction discs are separated inside a clear 10 m area at the active place. Solid props avoid those areas and the 4 m corridors along all declared paths. These connected paths join the clear areas. Runtime collision discs conservatively contain the scenery models. Rivers are shallow visual water and do not block or damage the player.

A command triggers on entering its 0.72 m contact disc or by pressing E within 2.1 m. Combat additionally provides buttons and number keys for all offered maneuvers and targets. Terminal states provide no graph command.

These are checked geometry and implementation tests, not a formal proof of all browser rendering and physics behavior. The environment tests execute the actual movement code along every declared trail in the example worlds and into every offered option.

## 6. Resolution and persistence

The browser sends `β(p)` to `/api/input`. Lean resolves it and returns the new view and reports. Inputs are locked during the request and report playback, preventing duplicate submissions. The server independently rejects commands outside `Game.inputs` without consuming dice or changing logical state.

The static environment, player position and camera persist across scene transitions. The next scene's current options appear at its mapped place. If that place is different, the player walks there. The mini-map and objective distance guide this trip. A fresh adventure may set a new spawn.

Combat animations present the engine reports in order. They never invent die faces, injury, range bonuses or a different result. With the same seed and command sequence, the spatial interface and the previous interface use the same logical execution.

## 7. Statistical clock and uniform test player

One fairness turn is one scene choice with its entire fight. It is not a frame, second, key press or individual combat maneuver.

In scenes, the test player uses `πU(a|s) = 1/|A(s)|`. In fights, the existing simulator selects a maneuver uniformly, then a living target uniformly when required. Uniformly selecting flattened maneuver/target pairs would be a different policy and is not used.

A human remains free to choose. Random movement keys do not simulate uniform graph-edge choices.

## 8. Preservation statement

Let `τn` be the instant of the nth logical command. Between these instants the projection stays constant. On resolution:

`P(α(Wafter)=s' | Wbefore=w, chosen a) = K(α(w),a,s')`.

Under the same decision policy and dice distribution, erasing movement and animations leaves the same logical traces, provided the chosen commands are eventually reached and resolved. Hence any criterion on those traces has the same probability after projection. This statement does not apply to criteria expressed in physical seconds or to future position-dependent combat rules.

The implemented contract combines the unchanged Lean input guarantees with an audited adapter and navigation tests. It is not an end-to-end theorem about WebGL or the browser.

## 9. Difficulty and admission

New Wishes select one of three shape-two Weibull reference curves. At ten scene choices their survival targets are 50%, 30% and 10%. The rational parameters, approximation theorem and limitations of statistical admission are documented in [Wish-generated worlds](wish-worlds.md).

The server tests 1,000 uniform-player games through 15 choices, using the existing confidence intervals, row definitions and tolerance. Scene walking and environment construction do not participate in those simulations. The geometry of a new world does not require probabilistic model checking of 3D physics.
