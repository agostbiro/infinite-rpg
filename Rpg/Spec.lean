import Rpg.Adventure

/-!
# Adventure legality under an explicit ruleset

The same rules value is used by the checker, the engine, and the probability graph.
Character and creature limits, point budgets, modifier bounds, and possible attacks
are evaluated using that adventure's rules. Shared structural constraints require
valid links, unique scene IDs, an ending, nonempty fights, and reachable scenes.

`LegalAdventure` covers the story; `LegalCharacter` covers its player character.
`Probability.AdventureDefinition` requires both proofs for the same rules and hero.
The separate probabilistic fairness policy is in `Rpg/Probability/Fairness.lean`.
-/

namespace Rpg

/-- Every skill entry of a being is bought at a level that can be bought,
and no skill is listed twice. -/
def SkillsWellBought (rules : RuleSet) (b : Being) : Prop :=
  (∀ e ∈ b.skills, (rules.skillStep b e.1 e.2).isSome) ∧
  (b.skills.map (·.1)).Nodup

/-- A Creature is a legal build. -/
def LegalCreature (rules : RuleSet) (b : Being) : Prop :=
  -- Each base attribute is within this adventure’s creature bounds.
  (∀ a ∈ [b.st, b.dx, b.iq, b.ht], rules.creatureAttributeMin ≤ a ∧ a ≤ rules.creatureAttributeMax) ∧
  -- Its cost is within this adventure’s creature budget.
  rules.points b ≤ rules.creaturePointLimit ∧
  -- Its skills are bought correctly.
  SkillsWellBought rules b ∧
  -- Its ST is high enough for its weapon.
  rules.minST b.weapon ≤ b.st

/-- The Character is a legal build. -/
def LegalCharacter (rules : RuleSet) (c : Being) : Prop :=
  -- Each base attribute is within this adventure’s character bounds.
  (∀ a ∈ [c.st, c.dx, c.iq, c.ht], rules.characterAttributeMin ≤ a ∧ a ≤ rules.characterAttributeMax) ∧
  -- Its cost matches this adventure’s character budget.
  rules.points c = rules.characterPoints ∧
  -- Its skills are bought correctly.
  SkillsWellBought rules c ∧
  -- Its ST is high enough for its weapon.
  rules.minST c.weapon ≤ c.st ∧
  -- Its natural DR is within the adventure’s limit.
  c.naturalDR ≤ rules.characterNaturalDRLimit

/-- At least one participant can injure the other under the selected rules.
This is a local possibility check, not a proof of eventual combat termination. -/
def FightCanEnd (rules : RuleSet) (c foe : Being) : Prop :=
  rules.canHurt c foe ∨ rules.canHurt foe c

instance (rules : RuleSet) (c foe : Being) : Decidable (FightCanEnd rules c foe) := by
  unfold FightCanEnd; infer_instance

/-- A Scene with this number exists in the Adventure. -/
def SceneExists (a : Adventure) (id : SceneId) : Prop :=
  id ∈ a.scenes.map (·.id)

instance (a : Adventure) (id : SceneId) : Decidable (SceneExists a id) := by
  unfold SceneExists; infer_instance

/-- A Choice in Scene `s` leads to Scene `t`. -/
def Leads (a : Adventure) (s t : SceneId) : Prop :=
  ∃ sc ∈ a.scenes, sc.id = s ∧ ∃ ch ∈ sc.choices, t ∈ ch.outcome.targets

/-- Scene `t` can be reached from the start Scene by following Choices. -/
inductive Reachable (a : Adventure) : SceneId → Prop where
  /-- The start Scene can be reached. -/
  | start : Reachable a a.start
  /-- If `s` can be reached and a Choice in `s` leads to `t`, then `t` can be reached. -/
  | next {s t : SceneId} : Reachable a s → Leads a s t → Reachable a t

/-- A Choice's Outcome is legal, for the Character `c`. -/
def LegalOutcome (rules : RuleSet) (c : Being) (a : Adventure) (o : Outcome) : Prop :=
  -- Every Scene it leads to exists.
  (∀ t ∈ o.targets, SceneExists a t) ∧
  -- A Success Roll uses this adventure’s modifier bounds.
  (match o with
    | .roll _ m _ _ => rules.modifierMin ≤ m ∧ m ≤ rules.modifierMax
    | _ => True) ∧
  -- A Fight has at least one Creature.
  (match o with
    | .fight fs _ => fs ≠ []
    | _ => True) ∧
  -- Every Creature is a legal build, and the Fight against it can end.
  (∀ f ∈ o.foes, LegalCreature rules f ∧ FightCanEnd rules c f)

/-- An Adventure is legal for the Character `c`. -/
def LegalAdventure (rules : RuleSet) (c : Being) (a : Adventure) : Prop :=
  -- The start Scene exists.
  SceneExists a a.start ∧
  -- No two Scenes share a number.
  (a.scenes.map (·.id)).Nodup ∧
  -- At least one Scene is an Ending.
  (∃ s ∈ a.scenes, s.choices = []) ∧
  -- Every Choice in every Scene is legal.
  (∀ s ∈ a.scenes, ∀ ch ∈ s.choices, LegalOutcome rules c a ch.outcome) ∧
  -- Every Scene can be reached from the start Scene.
  (∀ s ∈ a.scenes, Reachable a s.id)

end Rpg
