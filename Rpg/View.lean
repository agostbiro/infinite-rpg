import Rpg.Map

/-!
# View

The view is everything the page draws, as JSON (JavaScript Object Notation):
the Scene or Fight, the Character panel, the map, every Report since the game began,
and the inputs the game offers now. The page sends back one of these inputs, as it is.
-/

namespace Rpg

open Lean

/-- Basic Speed as text with two decimals, such as "6.00". -/
def speedText (b : Being) : String :=
  let x := b.speedX4
  s!"{x / 4}.{["00", "25", "50", "75"].getD (x % 4) "00"}"

/-- The name of a type of armor, for display. -/
def Armor.name : Armor → String
  | .none => "no armor"
  | .leather => "leather armor"

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

/-- The Character panel: attributes, skills, Gear, and HP. -/
def characterJson (b : Being) (hp : Int) : Json :=
  json% {
    name: $(b.name), st: $(b.st), dx: $(b.dx), iq: $(b.iq), ht: $(b.ht),
    hp: $(hp), maxHP: $(b.maxHP), dodge: $(b.dodge), speed: $(speedText b),
    skills: $(b.skills.map fun (s, l) => json% { name: $(s.name), level: $(l) }),
    weapon: $(b.weapon.name),
    damage: $(s!"{(b.weapon.damage b.st).show} {b.weapon.damageType.name}"),
    attack: $(b.attackLevel),
    armor: $(b.armor.name), dr: $(b.dr)
  }

/-- One being in a Fight, for its card. -/
def fighterJson (who : Actor) (f : Fighter) : Json :=
  json% {
    actor: $(who), name: $(f.being.name), hp: $(f.hp), maxHP: $(f.being.maxHP),
    alive: $(f.alive), maneuver: $(f.maneuver.label), weapon: $(f.being.weapon.name),
    damage: $(s!"{(f.being.weapon.damage f.being.st).show} {f.being.weapon.damageType.name}"),
    attack: $(f.being.attackLevel), dodge: $(f.dodge), dr: $(f.being.dr)
  }

/-- The Fight part of the view. Each Maneuver lists the inputs it offers. -/
def fightJson (offered : List Input) (f : FightPhase) : Json :=
  let maneuvers := maneuverMenu.map fun m =>
    let options := offered.filterMap fun i =>
      match i with
      | .maneuver m' t => if m' = m then some (json% { target: $(t), input: $(i) }) else none
      | _ => none
    json% { label: $(m.label), help: $(m.help), attacks: $(m.attacks), options: $(options) }
  json% {
    round: $(f.round),
    hero: $(fighterJson none f.state.hero),
    foes: $(f.state.foes.zipIdx.map fun (x, i) => fighterJson (some i) x),
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
      picture: $(sc.picture.filter safePicture),
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
  let fight := match g.phase with
    | .fight f => fightJson g.inputs f
    | .dead f => fightJson [] f
    | _ => Json.null
  json% {
    seed: $(seed),
    adventure: $(g.adventure.title),
    phase: $(g.phase.name),
    character: $(characterJson g.hero hp),
    scene: $(match g.sceneId? with | some id => sceneJson g id | none => Json.null),
    fight: $(fight),
    map: $(g.map),
    inputs: $(g.inputs),
    reports: $(reports),
    fresh: $(fresh),
    error: $(error)
  }

end Rpg
