import Rpg.Map
import Rpg.SpatialProjection

/-!
# View

The view is everything the page draws, as JSON (JavaScript Object Notation):
the Scene or Fight, the Character panel, the map, every Report since the game began,
and the inputs the game offers now. The page sends back one of these inputs, as it is.

The view shows each skill, weapon, and armor by its Theme Name, if the Adventure gives one,
and else by its rule name. The Theme Name is shown alone, never next to the rule name.
-/

namespace Rpg

open Lean

/-- Basic Speed as text with two decimals, such as "6.00". -/
def speedText (rules : RuleSet) (b : Being) : String :=
  let x := rules.speedX4 b
  s!"{x / 4}.{["00", "25", "50", "75"].getD (x % 4) "00"}"

/-- The name of a Maneuver for a button. -/
def Maneuver.label : Maneuver → String
  | .attack => "Attack"
  | .allOutAttack => "All-Out Attack"
  | .allOutDefense => "All-Out Defense"

/-- What a Maneuver does, for the button's help line. -/
def Maneuver.help : Maneuver → String
  | .attack => "Attack, and Dodge as usual."
  | .allOutAttack => "+4 to hit, but no Dodge until your next turn."
  | .allOutDefense => "No attack, but +2 to Dodge until your next turn."

/-- The name of a Success Roll that the Player sees, such as "DX -2" or "Wand Duelling".
A skill shows its Theme Name. -/
def rollText (th : ThemeNames) (t : RollTarget) (m : Int) : String :=
  let name := match t with
    | .skill s => th.skill s
    | .attribute a => a.name
  if m = 0 then name else if m > 0 then s!"{name} +{m}" else s!"{name} {m}"

/-- How an attack names its weapon, such as "with a broadsword", "with bare fists", or
"with Sting" for a weapon with a Theme Name. -/
def withWeaponText (th : ThemeNames) (w : Weapon) : String :=
  match th.weapons.lookup w with
  | some name => s!"with {name}"
  | none => if w = .punch then "with bare fists" else s!"with a {w.name}"

/-- The damage of a being's weapon as text, such as "1d+2 cutting". -/
def damageText (rules : RuleSet) (b : Being) : String :=
  s!"{(rules.weaponDice b).show} {b.weapon.damageType.name}"

/-- Local equipment names apply to their owner, without renaming other beings' weapons. -/
def weaponText (rules : RuleSet) (th : ThemeNames) (b : Being) : String :=
  ((rules.equipmentFor b).map (·.name)).getD (th.weapon b.weapon)

/-- The Character panel: attributes, skills, Gear, and HP. Names are Theme Names. -/
def characterJson (rules : RuleSet) (th : ThemeNames) (b : Being) (hp : Int) : Json :=
  json% {
    name: $(b.name), st: $(b.st), dx: $(b.dx), iq: $(b.iq), ht: $(b.ht),
    hp: $(hp), maxHP: $(rules.maxHP b), dodge: $(rules.dodge b), speed: $(speedText rules b),
    skills: $(b.skills.map fun (s, l) => json% { name: $(th.skill s), level: $(l) }),
    weapon: $(weaponText rules th b),
    damage: $(damageText rules b),
    attack: $(rules.weaponLevel b),
    armor: $(th.armorName b.armor), dr: $(rules.dr b)
  }

/-- One being in a Fight, for its card. -/
def fighterJson (rules : RuleSet) (th : ThemeNames) (who : Actor) (f : Fighter) : Json :=
  json% {
    actor: $(who), name: $(f.being.name), hp: $(f.hp), maxHP: $(rules.maxHP f.being),
    alive: $(f.alive), maneuver: $(f.maneuver.label), weapon: $(weaponText rules th f.being),
    damage: $(damageText rules f.being),
    attack: $(rules.weaponLevel f.being), dodge: $(f.dodge rules), dr: $(rules.dr f.being)
  }

/-- A card at the start of a Fight, with the weapon's Theme Name. -/
def cardJson (th : ThemeNames) (c : Card) : Json :=
  json% {
    name: $(c.name), hp: $(c.hp), maxHP: $(c.maxHP), weapon: $(c.equipmentName.getD (th.weapon c.weapon)),
    damage: $(c.damage), dr: $(c.dr)
  }

/-- A Report as the page gets it. A roll names its skill and an attack names its weapon by the
Theme Name. Every other Report is sent as it is. -/
def reportJson (th : ThemeNames) : Report → Json
  | .successRoll who t m roll =>
    json% { successRoll: { who: $(who), what: $(rollText th t m), roll: $(roll) } }
  | .cannotTry who t m level =>
    json% { cannotTry: { who: $(who), what: $(rollText th t m), level: $(level) } }
  | .attack attacker attackerName defender defenderName w equipmentName roll =>
    json% { attack: {
      attacker: $(attacker), attackerName: $(attackerName), defender: $(defender),
      defenderName: $(defenderName), weapon: $(equipmentName.getD (th.weapon w)),
      withWeapon: $(equipmentName.map (fun name => s!"with {name}") |>.getD (withWeaponText th w)),
      roll: $(roll) } }
  | .fightStarts hero foes =>
    json% { fightStarts: { hero: $(cardJson th hero), foes: $(foes.map (cardJson th)) } }
  | r => toJson r

/-- Preview conditional effects of a maneuver against at least one living opponent. -/
def maneuverEffects (rules : RuleSet) (f : FightPhase) (m : Maneuver) : List String :=
  let hero := { f.state.hero with maneuver := m }
  (rules.combatRules.filter fun r => f.state.foes.zipIdx.any fun (foe, i) =>
    foe.alive && (r.active rules none hero foe || r.active rules (some i) foe hero)).map
      (fun r => s!"{r.name}: {r.description}")

/-- The Fight part of the view. Each Maneuver lists its inputs and active tactical effects. -/
def fightJson (rules : RuleSet) (th : ThemeNames) (offered : List Input) (f : FightPhase) : Json :=
  let maneuvers := maneuverMenu.map fun m =>
    let options := offered.filterMap fun i =>
      match i with
      | .maneuver m' t => if m' = m then some (json% { target: $(t), input: $(i) }) else none
      | _ => none
    json% { label: $(m.label), help: $(m.help), effects: $(maneuverEffects rules f m),
      attacks: $(m.attacks), options: $(options) }
  json% {
    round: $(f.round),
    hero: $(fighterJson rules th none f.state.hero),
    foes: $(f.state.foes.zipIdx.map fun (x, i) => fighterJson rules th (some i) x),
    maneuvers: $(maneuvers)
  }

/-- The current Scene. Its Choices carry their inputs while the game offers them. -/
def sceneJson (g : Game) (id : SceneId) : Json :=
  match g.adventure.scene? id with
  | none => Json.null
  | some sc =>
    let offered := g.inputs
    let choices := sc.choices.zipIdx.map fun (ch, k) =>
      let i := Input.choose k
      json% { text: $(ch.text), input: $(if i ∈ offered then toJson i else Json.null) }
    json% {
      id: $(id), title: $(sc.title), text: $(sc.text),
      ending: $(sc.choices.isEmpty), choices: $(choices)
    }

/-- The whole view. `reports` are all the Reports since the game began, and `fresh` is how
many of them at the end are new since the last view. `error` is set for a refused input. -/
def viewJson (g : Game) (seed : Nat) (reports : Array Report) (fresh : Nat)
    (error : Option String) : Json :=
  let hp := match g.phase with
    | .fight f => f.state.hero.hp
    | .dead f => f.state.hero.hp
    | _ => g.hp
  let th := g.adventure.themes
  let fight := match g.phase with
    | .fight f => fightJson g.rules th g.inputs f
    | .dead f => fightJson g.rules th [] f
    | _ => Json.null
  json% {
    seed: $(seed),
    spatialGraph: $(g.spatialProjection),
    adventure: $(g.adventure.title),
    phase: $(g.phase.name),
    character: $(characterJson g.rules th g.hero hp),
    scene: $(match g.sceneId? with | some id => sceneJson g id | none => Json.null),
    fight: $(fight),
    map: $(g.map),
    inputs: $(g.inputs),
    reports: $(reports.map (reportJson th)),
    fresh: $(fresh),
    error: $(error)
  }

/-! ## Tests -/

/-- Theme Names for a test: Broadsword is "Wand Duelling" and the broadsword is "Sting". -/
private def testThemes : ThemeNames :=
  { skills := [(.broadsword, "Wand Duelling")], weapons := [(.broadsword, "Sting")] }

-- A roll shows the Theme Name alone. A thing with no Theme Name shows its rule name.
#guard rollText testThemes (.skill .broadsword) (-2) == "Wand Duelling -2"
#guard rollText testThemes (.skill .stealth) 0 == "Stealth"
#guard rollText testThemes (.attribute .dx) 1 == "DX +1"
#guard withWeaponText testThemes .broadsword == "with Sting"
#guard withWeaponText {} .broadsword == "with a broadsword"
#guard withWeaponText {} .punch == "with bare fists"

-- The roll Report keeps the rule data, but the page gets the Theme Name.
#guard
  let r := Report.successRoll "Mara" (.skill .broadsword) 0 ⟨[1, 2, 3], 6, 14, .success⟩
  (reportJson testThemes r).getObjValD "successRoll" |>.getObjValD "what" == Json.str "Wand Duelling"

end Rpg
