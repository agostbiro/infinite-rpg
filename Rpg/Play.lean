import Rpg.InputSpec

/-!
# Play

`step` moves a game forward by one input from the Player. It is pure: dice come from the
seeded `Rng` in the `Roll` monad, so the same seed and the same inputs always give the same game.

`Game.inputs` lists the inputs the game offers now. The page shows one button for each.
Three theorems tie them to the rules:

* `inputs_allowed` and `inputs_complete`: the inputs in `Game.inputs` are exactly the inputs that
  `AllowedInput` (the spec) allows. `mem_inputs_iff` puts the two together.
* `step_rejects`: `step` refuses any other input. The game and the dice stay as they were.

In a Fight, one `step` runs the Character's turn and then every Creature turn up to the
Character's next turn. The turn order is a finite list, so this needs no loop.
-/

namespace Rpg

/-! ## Inputs -/

/-- The Maneuvers the Player can choose, in menu order. -/
def maneuverMenu : List Maneuver := [.attack, .allOutAttack, .allOutDefense]

/-- The inputs for the Character's turn in a Fight. A Maneuver that attacks has one input
for each living Creature. A Maneuver with no attack has one input with no target. -/
def fightInputs (s : FightState) : List Input :=
  maneuverMenu.flatMap fun m =>
    if m.attacks then s.livingFoes.map fun t => .maneuver m (some t)
    else [.maneuver m none]

/-- The inputs the game offers now. -/
def Game.inputs (g : Game) : List Input :=
  match g.phase with
  | .title => [.begin]
  | .scene id =>
    match g.adventure.scene? id with
    | some sc => (List.range sc.choices.length).map .choose
    | none => []
  | .fight f => if f.state.over then [] else fightInputs f.state
  | .ended _ => []
  | .dead _ => []

/-! ## Moving through Scenes -/

/-- Go to Scene `id`. Returns the game in that Scene, and a Report with the Scene's text.
At an Ending, the Adventure is over. -/
def Game.enter (g : Game) (id : SceneId) : Game × List Report :=
  match g.adventure.scene? id with
  | some sc =>
    let ending := sc.choices.isEmpty
    let report := Report.scene id sc.title sc.text ending (sc.picture.filter safePicture)
    ({ g with phase := if ending then .ended id else .scene id }, [report])
  -- A Legal Adventure has no missing Scenes. The game offers no inputs here.
  | none => ({ g with phase := .scene id }, [])

/-- Record that Choice `k` of Scene `id` led to Scene `target`. -/
def Game.record (g : Game) (id : SceneId) (k : Nat) (target : SceneId) (rolled : Option Bool) : Game :=
  { g with trail := g.trail ++ [⟨id, k, target, rolled⟩] }

/-! ## Fights -/

/-- After the Creature turns: the Character died, or won, or has the next turn. -/
def Game.settle (g : Game) (f : FightPhase) : Game × List Report :=
  let g := { g with hp := f.state.hero.hp }
  if !f.state.hero.alive then
    ({ g with phase := .dead f }, [.died g.hero.name])
  else if f.state.foes.all (!·.alive) then
    let (g, reports) := (g.record f.scene f.choice f.onWin none).enter f.onWin
    (g, .fightWon :: reports)
  else
    ({ g with phase := .fight f }, [])

/-- Start a Fight from Choice `k` of Scene `id`. The Creatures that are faster than the
Character act first. -/
def Game.startFight (g : Game) (id : SceneId) (k : Nat) (foes : List Being) (onWin : SceneId) :
    Roll (Game × List Report) := do
  let order := turnOrder g.rules g.hero foes
  let s : FightState :=
    { hero := { being := g.hero, hp := g.hp }, foes := foes.map fun b => { being := b, hp := g.rules.maxHP b } }
  let (s, first) ← foeTurns g.rules s (beforeCharacter order)
  let (g, last) := g.settle ⟨id, k, onWin, order, 1, s⟩
  let cards := foes.map fun b => b.card g.rules (g.rules.maxHP b)
  return (g, [.fightStarts (g.hero.card g.rules g.hp) cards, .round 1] ++ first ++ last)

/-- The Character's turn with Maneuver `m` at `target`. Then every Creature turn up to the
Character's next turn: the rest of this round, and the start of the next round. -/
def Game.characterTurn (g : Game) (f : FightPhase) (m : Maneuver) (target : Option Nat) :
    Roll (Game × List Report) := do
  let (s, mine) ← heroTurn g.rules f.state m (target.getD 0)
  let (s, after) ← foeTurns g.rules s (afterCharacter f.order)
  let (s, round, next) ←
    if s.over then pure (s, f.round, [])
    else do
      let (s, before) ← foeTurns g.rules s (beforeCharacter f.order)
      pure (s, f.round + 1, .round (f.round + 1) :: before)
  let (g, last) := g.settle { f with state := s, round }
  return (g, mine ++ after ++ next ++ last)

/-! ## One step -/

/-- Pick Choice `ch`, number `k` in Scene `id`. -/
def Game.choose (g : Game) (id : SceneId) (k : Nat) (ch : Choice) : Roll (Game × List Report) := do
  let picked := Report.picked ch.text
  match ch.outcome with
  | .goto n =>
    let (g, reports) := (g.record id k n none).enter n
    return (g, picked :: reports)
  | .roll t m onSuccess onFailure =>
    let (res, roll) ← makeRoll g.rules g.hero.name t m ((g.rules.rollLevel g.hero t).map (· + m))
    let n := if res.succeeded then onSuccess else onFailure
    let (g, reports) := (g.record id k n (some res.succeeded)).enter n
    return (g, picked :: roll :: reports)
  | .fight foes onWin =>
    let (g, reports) ← g.startFight id k foes onWin
    return (g, picked :: reports)

/-- Apply an input. `step` calls this only for an input in `Game.inputs`. -/
def Game.apply (g : Game) (i : Input) : Roll (Game × List Report) :=
  match g.phase, i with
  | .title, .begin => return g.enter g.adventure.start
  | .scene id, .choose k =>
    match (g.adventure.scene? id).bind (·.choices[k]?) with
    | some ch => g.choose id k ch
    | none => return (g, [])
  | .fight f, .maneuver m target => g.characterTurn f m target
  | _, _ => return (g, [])

/-- The text of the Report for a refused input. -/
def rejectedWhy : String := "The game does not offer this input now."

/-- Move the game forward by one input. An input that the game does not offer is refused:
the game stays as it was, no dice are rolled, and the only Report says so. -/
def step (g : Game) (i : Input) : Roll (Game × List Report) :=
  if i ∈ g.inputs then g.apply i
  else return (g, [.rejected rejectedWhy])

/-! ## The two input theorems -/

/-- **`step` refuses every input that the game does not offer.** The game and the dice
(`Rng`) stay as they were, and the only Report says the input was refused. -/
theorem step_rejects (g : Game) (i : Input) (dice : Rng)
    -- The game does not offer `i` now.
    (h : i ∉ g.inputs) :
    (step g i).run dice = ((g, [.rejected rejectedWhy]), dice) := by
  simp only [step, h, ↓reduceIte]
  rfl

/-- A Fight that is not over goes on. -/
theorem goesOn_of_not_over {s : FightState}
    -- The Fight is not over.
    (h : s.over = false) :
    FightGoesOn s := by
  simp [FightState.over] at h
  exact h

/-- A Creature number in `livingFoes` names a living Creature. -/
theorem mem_livingFoes {s : FightState} {t : Nat}
    -- `t` is in the list of living Creatures.
    (h : t ∈ s.livingFoes) :
    ∃ foe, s.foes[t]? = some foe ∧ foe.alive = true := by
  simp only [FightState.livingFoes, List.mem_filter, List.mem_range] at h
  obtain ⟨_, halive⟩ := h
  cases hfoe : s.foes[t]? with
  -- There is no Creature number `t`: then `t` is not in the list.
  | none => simp [hfoe] at halive
  -- Creature number `t` is `foe`, and the filter says it is alive.
  | some foe => exact ⟨foe, rfl, by simpa [hfoe] using halive⟩

/-- Every input for a Fight is allowed, while the Fight goes on. -/
theorem fightInputs_allowed {g : Game} {f : FightPhase} {i : Input}
    -- The game is in the Fight `f`.
    (hphase : g.phase = .fight f)
    -- The Fight goes on.
    (hon : FightGoesOn f.state)
    -- `i` is one of the inputs for this Fight.
    (h : i ∈ fightInputs f.state) :
    AllowedInput g i := by
  simp [fightInputs, maneuverMenu, Maneuver.attacks] at h
  rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | rfl
  all_goals unfold AllowedInput; rw [hphase]
  -- An Attack on a living Creature.
  · exact ⟨hon, rfl, mem_livingFoes ht⟩
  -- An All-Out Attack on a living Creature.
  · exact ⟨hon, rfl, mem_livingFoes ht⟩
  -- All-Out Defense, with no target.
  · exact ⟨hon, rfl⟩

/-- **Every input that the game offers is allowed by the rules.** -/
theorem inputs_allowed {g : Game} {i : Input}
    -- The game offers `i` now.
    (h : i ∈ g.inputs) :
    AllowedInput g i := by
  unfold Game.inputs at h
  split at h
  -- The title screen offers only `begin`.
  · rename_i hphase
    simp only [List.mem_singleton] at h
    subst h
    unfold AllowedInput
    rw [hphase]
    trivial
  -- A Scene offers one input for each of its Choices.
  · rename_i id hphase
    split at h
    · rename_i sc hsc
      simp only [List.mem_map, List.mem_range] at h
      obtain ⟨k, hk, rfl⟩ := h
      unfold AllowedInput
      rw [hphase]
      exact ⟨sc, hsc, hk⟩
    · simp at h
  -- A Fight offers the Fight inputs, but only while the Fight goes on.
  · rename_i f hphase
    split at h
    · simp at h
    · rename_i hover
      exact fightInputs_allowed hphase (goesOn_of_not_over (by simpa using hover)) h
  -- After an Ending, nothing is offered.
  · simp at h
  -- After the Character's death, nothing is offered.
  · simp at h

/-- A Fight that goes on is not over. -/
theorem not_over_of_goesOn {s : FightState}
    -- The Fight goes on.
    (h : FightGoesOn s) :
    s.over = false := by
  obtain ⟨hhero, foe, hmem, halive⟩ := h
  simp only [FightState.over, hhero, Bool.not_true, Bool.false_or, List.all_eq_false]
  exact ⟨foe, hmem, by simp [halive]⟩

/-- A living Creature is in `livingFoes`. -/
theorem mem_livingFoes_of {s : FightState} {t : Nat} {foe : Fighter}
    -- Creature number `t` is `foe`.
    (hfoe : s.foes[t]? = some foe)
    -- `foe` is alive.
    (halive : foe.alive = true) :
    t ∈ s.livingFoes := by
  simp only [FightState.livingFoes, List.mem_filter, List.mem_range]
  refine ⟨?_, by simp [hfoe, halive]⟩
  exact (List.getElem?_eq_some_iff.mp hfoe).1

/-- **The game offers every input that the rules allow.** -/
theorem inputs_complete {g : Game} {i : Input}
    -- The rules allow `i` now.
    (h : AllowedInput g i) :
    i ∈ g.inputs := by
  unfold AllowedInput at h
  split at h
  -- On the title screen, the game offers `begin`.
  · rename_i hphase
    simp [Game.inputs, hphase]
  -- In a Scene, the game offers each of its Choices.
  · rename_i id k hphase
    obtain ⟨sc, hsc, hk⟩ := h
    simp only [Game.inputs, hphase, hsc, List.mem_map, List.mem_range]
    exact ⟨k, hk, rfl⟩
  -- In a Fight, the game offers each attacking Maneuver at each living Creature.
  · rename_i f m t hphase
    obtain ⟨hon, hattacks, foe, hfoe, halive⟩ := h
    simp only [Game.inputs, hphase, not_over_of_goesOn hon, Bool.false_eq_true, ite_false]
    have ht := mem_livingFoes_of hfoe halive
    cases m <;> simp_all [fightInputs, maneuverMenu, Maneuver.attacks]
  -- In a Fight, the game offers All-Out Defense with no target.
  · rename_i f m hphase
    obtain ⟨hon, hattacks⟩ := h
    simp only [Game.inputs, hphase, not_over_of_goesOn hon, Bool.false_eq_true, ite_false]
    cases m <;> simp_all [fightInputs, maneuverMenu, Maneuver.attacks]
  -- No other input is allowed.
  · exact h.elim

/-- **The game offers exactly the inputs that the rules allow.** -/
theorem mem_inputs_iff {g : Game} {i : Input} : i ∈ g.inputs ↔ AllowedInput g i :=
  ⟨inputs_allowed, inputs_complete⟩

/-! ## Tests -/

-- Seed 7 gives the faces 4, 1, 1 for the first 3d6.
#guard ((rollDice 3).run' ⟨7⟩).run == [4, 1, 1]

-- The hypothesis of `inputs_allowed` can hold: The Shore offers its second Choice.
example : AllowedInput shoreGame (.choose 1) := inputs_allowed (by decide)

-- The hypothesis of `step_rejects` can hold: the title screen does not offer a Choice.
-- A refused input leaves the game and the dice as they were.
example : (step titleGame (.choose 0)).run ⟨7⟩ = ((titleGame, [.rejected rejectedWhy]), ⟨7⟩) :=
  step_rejects _ _ _ (by decide)

-- `begin` goes to The Shore and rolls no dice.
#guard
  let ((g, reports), dice) := (step titleGame .begin).run ⟨7⟩
  g.phase.name == "scene" && g.sceneId? == some 0 && dice.state == 7 &&
    reports.map (·.isRejected) == [false]

-- With seed 7, the goat path (DX -2, so 10 or less) rolls 4, 1, 1 = 6: a success. Mara reaches The Gallery.
#guard
  let (g, reports) := (step shoreGame (.choose 1)).run' ⟨7⟩
  g.sceneId? == some 2 && g.trail.map (·.rolled) == [some true] &&
    reports.contains (.successRoll "Mara" (.attribute .dx) (-2) ⟨[4, 1, 1], 6, 10, .success⟩)

-- In a Fight, a forged attack on a Creature that is down is refused.
#guard
  let (g, reports) := (step fightGame (.maneuver .attack (some 0))).run' ⟨7⟩
  g.phase.name == "fight" && reports == [.rejected rejectedWhy]

/-- Play the first input the game offers, at most `n` times. Returns the last game and all Reports. -/
def autoplay (g : Game) (dice : Rng) : Nat → Game × List Report
  | 0 => (g, [])
  | n + 1 =>
    match g.inputs with
    | [] => (g, [])
    | i :: _ =>
      let ((g, first), dice) := (step g i).run dice
      let (g, later) := autoplay g dice n
      (g, first ++ later)

-- For seeds 0 to 29, the game is over within 200 inputs, by an Ending or by death,
-- and the Engine never refuses an input it offered.
#guard (List.range 30).all fun seed =>
  let (g, reports) := autoplay titleGame ⟨seed.toUInt64⟩ 200
  g.inputs.isEmpty && (g.phase.name == "ended" || g.phase.name == "dead") &&
    !reports.any (·.isRejected)

end Rpg
