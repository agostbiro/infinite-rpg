import Rpg.Adventure

/-!
# Spec: what makes an Adventure legal

This file is the spec. Read it to know what "legal" means.
The checker in `Rpg/Check.lean` is proved to agree with it.

A Legal Adventure obeys these rules:

1. Every Creature is a legal build: attributes from 1 to 20, at most 150 points,
   each skill bought at a level that can be bought, each skill listed once, and ST high enough for its weapon.
2. Every Success Roll uses a modifier from -10 to +10, and the Character can try it:
   the Character can use the skill, and the effective skill is 3 or more.
   Then both results can happen, so both Scenes that the roll leads to can be reached in play.
3. Every Scene that a Choice leads to exists, and so does the start Scene. No two Scenes share a number.
4. At least one Scene is an Ending (it has no Choices).
5. Every Fight can end: for each Creature, the Character can hurt it, or it can hurt the Character.
   "Can hurt" means: the attack level is 3 or more, and the best possible hit gets past DR.
   A Fight must also have at least one Creature.
6. Every Scene can be reached from the start Scene by following Choices.
7. From every Scene, an Ending can be reached by following Choices.
   Each Scene that an Outcome can lead to counts, whatever the dice do.

These rules do not say that the Adventure is fair or can be won.
For example, a Fight that the Character cannot win is legal.
Rule 7 ignores the dice and the Fights. It does not say that the Character lives to reach an Ending.
Fairness is planned for a later version.

The Character must be a legal build too: attributes from 7 to 14, exactly 100 points, no natural DR.

Rules 1, 2, and 4 to 7, and the point caps, are design rules of this game, not GURPS rules.
They put limits on Creatures and rolls. They do not stop a strong Creature:
low attributes give points back, so a 150-point Creature can still be one the Character cannot hurt.

Theme Names (`Adventure.themes`) and Pictures change only what the Player sees. No rule here looks at them.
-/

namespace Rpg

/-- Every skill entry of a being is bought at a level that can be bought,
and no skill is listed twice. -/
def SkillsWellBought (b : Being) : Prop :=
  (∀ e ∈ b.skills, (b.skillStep e.1 e.2).isSome) ∧
  (b.skills.map (·.1)).Nodup

/-- A Creature is a legal build. -/
def LegalCreature (b : Being) : Prop :=
  -- Each attribute is from 1 to 20.
  (∀ a ∈ [b.st, b.dx, b.iq, b.ht], 1 ≤ a ∧ a ≤ 20) ∧
  -- It costs at most 150 points.
  b.points ≤ 150 ∧
  -- Its skills are bought correctly.
  SkillsWellBought b ∧
  -- Its ST is high enough for its weapon.
  b.weapon.minST ≤ b.st

/-- The Character is a legal build. -/
def LegalCharacter (c : Being) : Prop :=
  -- Each attribute is from 7 to 14.
  (∀ a ∈ [c.st, c.dx, c.iq, c.ht], 7 ≤ a ∧ a ≤ 14) ∧
  -- It costs exactly 100 points.
  c.points = 100 ∧
  -- Its skills are bought correctly.
  SkillsWellBought c ∧
  -- Its ST is high enough for its weapon.
  c.weapon.minST ≤ c.st ∧
  -- It has no natural DR.
  c.naturalDR = 0

/-- A Fight between the Character and a Creature can end: one of them can hurt the other. -/
def FightCanEnd (c foe : Being) : Prop :=
  c.canHurt foe ∨ foe.canHurt c

instance (c foe : Being) : Decidable (FightCanEnd c foe) := by
  unfold FightCanEnd; infer_instance

/-- The Character `c` can try a Success Roll against `t` at modifier `m`:
`c` can use the skill, and the effective skill is 3 or more (p. 2).
Then a roll of 3 always succeeds and a roll of 18 always fails, so both results can happen. -/
def CanTryRoll (c : Being) (t : RollTarget) (m : Int) : Prop :=
  match c.rollLevel t with
  | some level => 3 ≤ level + m
  | none => False

instance (c : Being) (t : RollTarget) (m : Int) : Decidable (CanTryRoll c t m) := by
  unfold CanTryRoll; split <;> infer_instance

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

/-- Scene `s` is an Ending: a Scene with this number has no Choices. -/
def IsEnding (a : Adventure) (s : SceneId) : Prop :=
  ∃ sc ∈ a.scenes, sc.id = s ∧ sc.choices = []

/-- An Ending can be reached from Scene `s` by following Choices. Dice do not count:
each Scene that an Outcome can lead to is a step. -/
inductive ReachesEnding (a : Adventure) : SceneId → Prop where
  /-- From an Ending, an Ending is reached. -/
  | ending {s : SceneId} : IsEnding a s → ReachesEnding a s
  /-- If a Choice in `s` leads to `t`, and an Ending can be reached from `t`, then also from `s`. -/
  | next {s t : SceneId} : Leads a s t → ReachesEnding a t → ReachesEnding a s

/-- A Choice's Outcome is legal, for the Character `c`. -/
def LegalOutcome (c : Being) (a : Adventure) (o : Outcome) : Prop :=
  -- Every Scene it leads to exists.
  (∀ t ∈ o.targets, SceneExists a t) ∧
  -- A Success Roll has a modifier from -10 to +10.
  (match o with
    | .roll _ m _ _ => -10 ≤ m ∧ m ≤ 10
    | _ => True) ∧
  -- The Character can try a Success Roll.
  (match o with
    | .roll t m _ _ => CanTryRoll c t m
    | _ => True) ∧
  -- A Fight has at least one Creature.
  (match o with
    | .fight fs _ => fs ≠ []
    | _ => True) ∧
  -- Every Creature is a legal build, and the Fight against it can end.
  (∀ f ∈ o.foes, LegalCreature f ∧ FightCanEnd c f)

/-- An Adventure is legal for the Character `c`. -/
def LegalAdventure (c : Being) (a : Adventure) : Prop :=
  -- The start Scene exists.
  SceneExists a a.start ∧
  -- No two Scenes share a number.
  (a.scenes.map (·.id)).Nodup ∧
  -- At least one Scene is an Ending.
  (∃ s ∈ a.scenes, s.choices = []) ∧
  -- Every Choice in every Scene is legal.
  (∀ s ∈ a.scenes, ∀ ch ∈ s.choices, LegalOutcome c a ch.outcome) ∧
  -- Every Scene can be reached from the start Scene.
  (∀ s ∈ a.scenes, Reachable a s.id) ∧
  -- From every Scene, an Ending can be reached.
  (∀ s ∈ a.scenes, ReachesEnding a s.id)

end Rpg
