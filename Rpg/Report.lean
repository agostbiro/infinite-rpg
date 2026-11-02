import Rpg.Adventure
import Lean.Data.Json

/-!
# Reports

A Report is one thing the Engine did or found out during play, such as a roll or a hit.
The Engine makes Reports, and the page draws them. A Report is data, not text,
so the page can draw each die face and move each HP bar.
Each Report that has dice carries every face the Engine rolled.
A Report keeps the rule data, such as the skill of a roll or the weapon of an attack.
The view (`Rpg/View.lean`) turns these into the Theme Names that the Player sees.
-/

namespace Rpg

open Lean

deriving instance ToJson, FromJson for Maneuver
deriving instance ToJson for RollResult
deriving instance ToJson for Attribute
deriving instance ToJson for Skill
deriving instance ToJson for RollTarget
deriving instance ToJson for Weapon
deriving instance ToJson for CombatRule

/-- Who acts in a Fight: `none` is the Character, `some i` is Creature number `i`. -/
abbrev Actor := Option Nat

/-- A roll of 3d6 against a target number. `total` is the sum of `faces`. -/
structure DiceRoll where
  faces : List Nat
  total : Nat
  target : Int
  result : RollResult
  deriving ToJson, BEq

/-- A damage roll as text, such as "1d+2" or "2d-1". -/
def Dice.show (d : Dice) : String :=
  if d.add > 0 then s!"{d.count}d+{d.add}"
  else if d.add < 0 then s!"{d.count}d{d.add}"
  else s!"{d.count}d"

/-- The name of a damage type, for display. -/
def DamageType.name : DamageType → String
  | .crushing => "crushing"
  | .cutting => "cutting"
  | .impaling => "impaling"
  | .burning => "burning"

/-- What the page shows on a being's card at the start of a Fight. -/
structure Card where
  name : String
  hp : Int
  maxHP : Nat
  weapon : Weapon
  /-- Snapshot the local equipment name so later changes do not rename earlier reports. -/
  equipmentName : Option String := none
  /-- The damage roll and type, such as "1d+2 cutting". -/
  damage : String
  dr : Nat
  deriving ToJson, BEq

/-- The card of a being with `hp` HP, under `rules`. -/
def Being.card (rules : RuleSet) (b : Being) (isHero : Bool) (hp : Int) : Card :=
  { name := b.name, hp, maxHP := rules.maxHP b, weapon := b.weapon,
    equipmentName := (rules.equipmentFor isHero b).map (·.name),
    damage := s!"{(rules.weaponDice isHero b).show} {b.weapon.damageType.name}", dr := rules.dr b }

/-- What the Player sees when the server puts a live change in play. The server makes it from the
admitted proposal, so it shows the gift and the rules that are now in force. -/
structure ChangeNote where
  /-- The Player's own words for the change. -/
  wish : String
  /-- The Dungeon Master's summary of the change. -/
  summary : String
  /-- The Dungeon Master's dramatic moment for the change. -/
  moment : String
  /-- The Character's card before the change. -/
  before : Card
  /-- The Character's card after the change. -/
  after : Card
  /-- The Character's attack level before the change. -/
  attackBefore : Int
  /-- The Character's attack level after the change. -/
  attackAfter : Int
  /-- `true` if the change gives the Character new equipment. -/
  equipment : Bool
  /-- The effects that the Player asked for. -/
  requested : List CombatRule
  /-- The counter-rules: the world's answer to the change. -/
  counter : List CombatRule
  /-- The number of Scenes that the change adds or replaces. -/
  scenes : Nat
  deriving ToJson, BEq

/-- One thing the Engine did or found out during play. -/
inductive Report where
  /-- The Character comes to a Scene. `ending` is true if the Scene is an Ending. -/
  | scene (id : SceneId) (title : String) (text : String) (ending : Bool)
  /-- The Player picks the Choice with this text. -/
  | picked (text : String)
  /-- `who` makes a Success Roll against `target` at `modifier`, for example DX at -2. -/
  | successRoll (who : String) (target : RollTarget) (modifier : Int) (roll : DiceRoll)
  /-- `who` cannot try a roll against `target` at `modifier`. `level` is the effective skill,
  or `none` if `who` cannot use the skill at all. The result is a failure. -/
  | cannotTry (who : String) (target : RollTarget) (modifier : Int) (level : Option Int)
  /-- A Fight starts between the Character and these Creatures, numbered from 0. -/
  | fightStarts (hero : Card) (foes : List Card)
  /-- A new round of the Fight starts. -/
  | round (n : Nat)
  /-- `who` chooses a Maneuver other than Attack. -/
  | maneuver (who : String) (m : Maneuver)
  /-- An attack roll by `attacker` on `defender`. -/
  | attack (attacker : Actor) (attackerName : String) (defender : Actor) (defenderName : String)
      (weapon : Weapon) (equipmentName : Option String) (roll : DiceRoll)
  /-- `who` cannot attack, because its effective skill `level` is below 3. -/
  | cannotAttack (who : String) (level : Int)
  /-- `who` cannot defend, because its last Maneuver was an All-Out Attack. -/
  | noDefense (who : String)
  /-- `who` tries to Dodge. A Dodge roll only succeeds or fails. -/
  | dodge (who : String) (roll : DiceRoll)
  /-- A hit on `defender`. `faces` are the damage dice, `add` is added to their sum.
  `maxed` is true after a roll of 3: every die counts as 6 and no dice are rolled.
  `hp` is the HP the defender has left. -/
  | damage (defender : Actor) (defenderName : String) (faces : List Nat) (maxed : Bool)
      (add : Int) (kind : String) (basic : Nat) (dr : Nat) (injury : Nat) (hp : Int)
  /-- `who` drops to 0 HP or less and is out of the Fight. -/
  | falls (who : Actor) (name : String)
  /-- Every Creature in the Fight is down. -/
  | fightWon
  /-- The Character died. The Adventure is over, but this is not an Ending. -/
  | died (who : String)
  /-- An adventure rule fires in a Fight. -/
  | worldRule (name : String) (text : String)
  /-- The server put a live change in play. -/
  | changeApplied (note : ChangeNote)
  /-- The Engine refused an input. Nothing changed. -/
  | rejected (why : String)
  deriving ToJson, BEq

/-- `true` if the Report says the Engine refused an input. -/
def Report.isRejected : Report → Bool
  | .rejected _ => true
  | _ => false

/-- Where an active combat rule comes from. "requested" means that a live change added it because
the Player asked for it. "counter" means that a live change added it as the world's answer.
"adventure" means that the Adventure had it from the start. -/
def ruleOrigin (reports : Array Report) (r : CombatRule) : String :=
  let notes := reports.filterMap fun
    | .changeApplied n => some n
    | _ => none
  if notes.any (·.requested.contains r) then "requested"
  else if notes.any (·.counter.contains r) then "counter"
  else "adventure"

end Rpg
