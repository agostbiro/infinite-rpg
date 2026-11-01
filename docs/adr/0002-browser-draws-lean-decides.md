# The browser draws, Lean decides

The game runs in a browser, but all rules and dice stay in Lean. A Lean program serves the page on `localhost` with core `Std.Http`. The Engine is a pure `step` function in `Rpg/`, and the server keeps the one current game in memory. The page only draws the view the server sends and sends back the Player's clicks. We do it this way so that the code the Player plays is the code the proofs are about, and so that the browser holds nothing that can change a roll.

## Considered options

- **Write the Engine again in JavaScript (JS), from an Adventure exported as JSON (JavaScript Object Notation).** Fast to build, but the game the Player plays would not be the verified one. Rejected.
- **Compile the Lean Engine to WebAssembly.** No server, but it needs the Emscripten compiler and much build work. Rejected for now.
- **A Lean web library (lean-fastapi, lean-routing).** The game needs about 4 routes and a static file handler, so a library saves under 100 lines and adds 5,000 to 30,000 lines of young code. Rejected.
- **Keep the terminal game next to the GUI (graphical user interface).** Rejected to keep one way to play. `make cheats` stays as a small program that prints the checker's errors.

## Consequences

- The page is outside the Engine and can send any input. `step` accepts only inputs that the game offers, and a theorem says any other input changes nothing. Another theorem says the game offers exactly the inputs the rules allow.
- Other websites in the Player's browser can send requests to `localhost` too. The server refuses every POST that is not JSON, and every POST whose `Origin` is not the game's own page.
- The page is trusted to show Reports as they are. Reports carry each die face, so the page never makes up dice.
- The server sends a CSP (Content Security Policy) header: scripts, styles, and images come only from the server.
- Since ADR 0006, the page draws the Adventure as a 3D world. It still sends only the inputs that the view offers, unchanged.
