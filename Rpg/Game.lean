import Rpg.Engine
import Rpg.Spec
import Rpg.Probability.Weibull

/-!
# Game

A `Game` records where play is: on the title screen, in a Scene, in a Fight,
or over. The function `step` in `Rpg/Play.lean` moves a `Game` forward by one input
from the Player. The page sends the inputs; it never changes a `Game` itself.

Only a Legal Adventure can be played. A `Game` holds a proof that its Adventure is legal for
its Character, and a proof that the Character is a legal build. So no code can make a `Game`
from an Adventure that has not passed the checker (or another proof).

A `Game` also holds the balance policy of its Adventure: the curve of its difficulty level.
A live change is checked against this policy, and it keeps the policy (`Prepared.game`).

This file has only the types. The spec for inputs is in `Rpg/InputSpec.lean`.
-/

namespace Rpg

open Lean

/-- One input from the Player. -/
inductive Input where
  /-- Start play from the title screen. -/
  | begin
  /-- Pick Choice number `choice` (counted from 0) in the current Scene. -/
  | choose (choice : Nat)
  /-- On the Character's turn in a Fight, use Maneuver `m`. If `m` attacks, `target` is the
  number of the Creature to attack. If `m` does not attack, `target` is `none`. -/
  | maneuver (m : Maneuver) (target : Option Nat)
  deriving DecidableEq, Repr, ToJson, FromJson

/-- A Choice that the Character took, and where it led. -/
structure Taken where
  /-- The Scene the Choice is in. -/
  source : SceneId
  /-- The number of the Choice in that Scene. -/
  choice : Nat
  /-- The Scene the Choice led to. -/
  target : SceneId
  /-- For a Success Roll: `some true` on success, `some false` on failure. Else `none`. -/
  rolled : Option Bool
  deriving DecidableEq, Repr

/-- A Fight that waits for the Character's turn. -/
structure FightPhase where
  /-- The Scene where the Fight started. -/
  scene : SceneId
  /-- The number of the Choice that started the Fight. -/
  choice : Nat
  /-- The Scene to go to if the Character wins. -/
  onWin : SceneId
  /-- The turn order. It does not change during the Fight. -/
  order : List Actor
  /-- The number of the round, from 1. -/
  round : Nat
  /-- The HP and last Maneuver of each being. -/
  state : FightState

/-- Where play is. -/
inductive Phase where
  /-- The title screen, before play starts. -/
  | title
  /-- In Scene `id`, which has Choices, waiting for the Player to pick one. -/
  | scene (id : SceneId)
  /-- In a Fight, on the Character's turn, waiting for the Player's Maneuver and target. -/
  | fight (f : FightPhase)
  /-- The Adventure is over: the Character reached the Ending `id`. -/
  | ended (id : SceneId)
  /-- The Adventure is over: the Character died in the Fight `f`. This is not an Ending. -/
  | dead (f : FightPhase)

/-- One game of an Adventure, played by one Character. -/
structure Game where
  /-- The rules of the Adventure. Checked live changes can replace local equipment and effects. -/
  rules : RuleSet
  /-- The Character. -/
  hero : Being
  /-- The Character is a legal build under `rules`. -/
  heroLegal : LegalCharacter rules hero
  /-- The Adventure. Checked live changes can replace future scenes. -/
  adventure : Adventure
  /-- The Adventure is legal for the Character under `rules`. -/
  legal : LegalAdventure rules hero adventure
  /-- The Character's HP now. -/
  hp : Int
  /-- Where play is. -/
  phase : Phase
  /-- Every Choice taken so far, oldest first. -/
  trail : List Taken
  /-- The balance policy of the Adventure: the curve of its difficulty level. A live change is
  checked against it and cannot change it. -/
  policy : Probability.BalancePolicy

/-- A new game on the title screen, with the Character at full HP and the balance policy `policy`.
It needs an `AdventureDefinition`, which holds the proofs that the Character and the Adventure
are legal under the rules. The server gets these proofs only from `checkCharacter_sound` and
`check_sound`, or from a shipped theorem such as `test_adventure_legal`. -/
def Game.new (d : AdventureDefinition)
    (policy : Probability.BalancePolicy := Probability.DifficultyLevel.medium.policy) : Game :=
  { rules := d.rules, hero := d.hero, heroLegal := d.heroLegal, adventure := d.story,
    legal := d.legal, hp := d.rules.maxHP d.hero, phase := .title, trail := [], policy }

/-- The Scene that play is in now, if any. In a Fight, this is the Scene where it started. -/
def Game.sceneId? (g : Game) : Option SceneId :=
  match g.phase with
  | .title => none
  | .scene id => some id
  | .fight f => some f.scene
  | .ended id => some id
  | .dead f => some f.scene

/-- The name of a phase, for the page and for tests. -/
def Phase.name : Phase → String
  | .title => "title"
  | .scene _ => "scene"
  | .fight _ => "fight"
  | .ended _ => "ended"
  | .dead _ => "dead"

/-- The numbers of the Creatures in a Fight that are alive. -/
def FightState.livingFoes (s : FightState) : List Nat :=
  (List.range s.foes.length).filter fun i => (s.foes[i]?.map (·.alive)).getD false

end Rpg
