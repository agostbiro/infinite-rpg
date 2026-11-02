import Rpg.Spec

/-!
# Checker

The checker reads an Adventure and returns a list of errors in plain words.
The DM reads these errors to fix a draft.

The main theorem is `check_sound`: if the checker finds no errors, the Adventure is legal by the spec.
-/

namespace Rpg

/-! ## Decision procedures for the spec

These let `decide` evaluate most of the spec directly. The illegal Adventures use them
to show that the spec itself rejects each cheat. -/

instance (rules : RuleSet) (b : Being) : Decidable (SkillsWellBought rules b) := by
  unfold SkillsWellBought; infer_instance

instance (rules : RuleSet) (b : Being) : Decidable (LegalCreature rules b) := by
  unfold LegalCreature; infer_instance

instance (rules : RuleSet) (c : Being) : Decidable (LegalCharacter rules c) := by
  unfold LegalCharacter; infer_instance

instance (rules : RuleSet) (c : Being) (a : Adventure) (o : Outcome) :
    Decidable (LegalOutcome rules c a o) := by
  unfold LegalOutcome; cases o <;> infer_instance

/-- No error if `p` is true, else one error with the message `msg`. -/
def need (p : Prop) [Decidable p] (msg : String) : List String :=
  if p then [] else [msg]

/-- The diagnostic is empty exactly when its independently stated condition holds. -/
@[simp] theorem need_eq_nil_iff {p : Prop} [Decidable p] {msg : String} :
    need p msg = [] ↔ p := by simp [need]

theorem need_sound {p : Prop} [Decidable p] {msg : String}
    (h : need p msg = []) : p := need_eq_nil_iff.mp h

/-- Errors in the skills of a being. -/
def checkSkills (rules : RuleSet) (b : Being) : List String :=
  need (∀ e ∈ b.skills, (rules.skillStep b e.1 e.2).isSome)
    s!"{b.name}: a skill level is too low to buy" ++
  need (b.skills.map (·.1)).Nodup
    s!"{b.name}: a skill is listed twice"

@[simp] theorem checkSkills_eq_nil_iff {rules : RuleSet} {b : Being} :
    checkSkills rules b = [] ↔ SkillsWellBought rules b := by
  simp [checkSkills, SkillsWellBought, List.append_eq_nil_iff]

theorem checkSkills_sound {rules : RuleSet} {b : Being}
    (h : checkSkills rules b = []) : SkillsWellBought rules b := checkSkills_eq_nil_iff.mp h

/-- Errors in the build of a Creature. -/
def checkCreature (rules : RuleSet) (b : Being) : List String :=
  need (∀ a ∈ [b.st, b.dx, b.iq, b.ht], rules.creatureAttributeMin ≤ a ∧ a ≤ rules.creatureAttributeMax)
    s!"{b.name}: each attribute must be from {rules.creatureAttributeMin} to {rules.creatureAttributeMax}" ++
  need (rules.points b ≤ rules.creaturePointLimit)
    s!"{b.name}: costs {rules.points b} points, but the limit is {rules.creaturePointLimit}" ++
  checkSkills rules b ++
  need (rules.minST b.weapon ≤ b.st)
    s!"{b.name}: ST {b.st} is too low for a {b.weapon.name} (needs {rules.minST b.weapon})"

@[simp] theorem checkCreature_eq_nil_iff {rules : RuleSet} {b : Being} :
    checkCreature rules b = [] ↔ LegalCreature rules b := by
  simp [checkCreature, LegalCreature, List.append_eq_nil_iff, and_assoc]

theorem checkCreature_sound {rules : RuleSet} {b : Being}
    (h : checkCreature rules b = []) : LegalCreature rules b := checkCreature_eq_nil_iff.mp h

/-- Errors in the build of the Character. -/
def checkCharacter (rules : RuleSet) (c : Being) : List String :=
  need (∀ a ∈ [c.st, c.dx, c.iq, c.ht], rules.characterAttributeMin ≤ a ∧ a ≤ rules.characterAttributeMax)
    s!"{c.name}: each attribute must be from {rules.characterAttributeMin} to {rules.characterAttributeMax}" ++
  need (rules.points c = rules.characterPoints)
    s!"{c.name}: costs {rules.points c} points, but must cost exactly {rules.characterPoints}" ++
  checkSkills rules c ++
  need (rules.minST c.weapon ≤ c.st)
    s!"{c.name}: ST {c.st} is too low for a {c.weapon.name} (needs {rules.minST c.weapon})" ++
  need (c.naturalDR ≤ rules.characterNaturalDRLimit)
    (if rules.characterNaturalDRLimit = 0 then s!"{c.name}: the Character cannot have natural DR"
     else s!"{c.name}: natural DR {c.naturalDR} is more than the limit of {rules.characterNaturalDRLimit}") ++
  need (0 < rules.maxHP c) s!"{c.name}: maximum HP must be positive so the Character starts alive"

@[simp] theorem checkCharacter_eq_nil_iff {rules : RuleSet} {c : Being} :
    checkCharacter rules c = [] ↔ LegalCharacter rules c := by
  simp [checkCharacter, LegalCharacter, List.append_eq_nil_iff, and_assoc]

theorem checkCharacter_sound {rules : RuleSet} {c : Being}
    (h : checkCharacter rules c = []) : LegalCharacter rules c := checkCharacter_eq_nil_iff.mp h

/-- Errors in the modifier of a Success Roll. -/
def checkModifier (rules : RuleSet) : Outcome → List String
  | .roll _ m _ _ => need (rules.modifierMin ≤ m ∧ m ≤ rules.modifierMax)
      s!"roll modifier {m} is not from {rules.modifierMin} to +{rules.modifierMax}"
  | _ => []

/-- Errors in a Success Roll that the Character `c` cannot try. -/
def checkCanTry (rules : RuleSet) (c : Being) : Outcome → List String
  | .roll t m _ _ =>
    need (CanTryRoll rules c t m)
      s!"{c.name} cannot try this {t.name} roll at {m}: the effective skill must be {rules.minimumRollLevel} or more"
  | _ => []

/-- Errors in the list of Creatures in a Fight. -/
def checkFoesNonempty : Outcome → List String
  | .fight fs _ => need (fs ≠ []) "a Fight has no Creatures"
  | _ => []

/-- Errors in one Creature of a Fight against the Character `c`. -/
def checkFoe (rules : RuleSet) (c f : Being) : List String :=
  checkCreature rules f ++
  need (DamagePossible rules c f)
    s!"{f.name}: the conservative damage screen found no injury in either direction (attack skill below {rules.minimumRollLevel}, or no hit can get past Dodge and DR)"

/-- Errors in the Outcome of a Choice. -/
def checkOutcome (rules : RuleSet) (c : Being) (a : Adventure) (o : Outcome) : List String :=
  o.targets.flatMap (fun t => need (SceneExists a t) s!"Scene {t} does not exist") ++
  checkModifier rules o ++
  checkCanTry rules c o ++
  checkFoesNonempty o ++
  o.foes.flatMap (checkFoe rules c)

/-- If `checkOutcome` finds no errors, the Outcome is legal. -/
theorem checkOutcome_sound {rules : RuleSet} {c : Being} {a : Adventure} {o : Outcome}
    (h : checkOutcome rules c a o = []) : LegalOutcome rules c a o := by
  simp only [checkOutcome, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨hTargets, hMod⟩, hTry⟩, hFoes⟩, hEach⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Every target Scene exists.
  · intro t ht
    exact need_sound (hTargets t ht)
  -- The roll modifier is in range.
  · cases o <;> first | trivial | exact need_sound hMod
  -- The Character can try a Success Roll.
  · cases o <;> first | trivial | exact need_sound hTry
  -- A Fight has at least one Creature.
  · cases o <;> first | trivial | exact need_sound hFoes
  -- Each Creature is legal and passes the damage screen.
  · intro f hf
    have hf' := hEach f hf
    simp only [checkFoe, List.append_eq_nil_iff] at hf'
    exact ⟨checkCreature_sound hf'.1, need_sound hf'.2⟩

/-! ## Reachability -/

/-- The Scenes that the Choices of Scene `s` lead to. -/
def successors (a : Adventure) (s : SceneId) : List SceneId :=
  (a.scenes.filter (·.id == s)).flatMap fun sc => sc.choices.flatMap (·.outcome.targets)

/-- A Scene in `successors a s` is one that a Choice in `s` leads to. -/
theorem leads_of_mem_successors {a : Adventure} {s t : SceneId}
    (h : t ∈ successors a s) : Leads a s t := by
  simp only [successors, List.mem_flatMap, List.mem_filter, beq_iff_eq] at h
  obtain ⟨sc, ⟨hsc, hid⟩, ch, hch, ht⟩ := h
  exact ⟨sc, hsc, hid, ch, hch, ht⟩

/-- Finite closure search shared by forward and backward reachability. -/
def exploreClosure (expand : List SceneId → List SceneId) : Nat → List SceneId → List SceneId
  | 0, seen => seen
  | fuel+1, seen =>
    let found := ((expand seen).filter (· ∉ seen)).eraseDups
    if found = [] then seen else exploreClosure expand fuel (seen ++ found)

/-- Any invariant preserved by expansion is preserved by the closure search. -/
theorem exploreClosure_invariant (expand : List SceneId → List SceneId) (P : SceneId → Prop)
    (step : ∀ seen, (∀ x ∈ seen, P x) → ∀ x ∈ expand seen, P x)
    (fuel : Nat) (seen : List SceneId) (initial : ∀ x ∈ seen, P x) :
    ∀ x ∈ exploreClosure expand fuel seen, P x := by
  induction fuel generalizing seen with
  | zero => exact initial
  | succ n ih =>
    simp only [exploreClosure]
    split
    · exact initial
    · apply ih
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact initial x hx
      · rw [List.mem_eraseDups] at hx
        exact step seen initial x (List.mem_filter.mp hx).1

/-- Forward expansion follows every outcome target. -/
def explore (a : Adventure) : Nat → List SceneId → List SceneId :=
  exploreClosure (fun seen => seen.flatMap (successors a))

theorem explore_reachable {a : Adventure} (fuel : Nat) (seen : List SceneId)
    (h : ∀ x ∈ seen, Reachable a x) : ∀ x ∈ explore a fuel seen, Reachable a x := by
  apply exploreClosure_invariant _ _ _ fuel seen h
  intro seen hs x hx
  obtain ⟨s, hmem, hedge⟩ := List.mem_flatMap.mp hx
  exact Reachable.next (hs s hmem) (leads_of_mem_successors hedge)

/-- The Scenes that the checker finds can be reached from the start. -/
def reachableScenes (a : Adventure) : List SceneId :=
  explore a (a.scenes.length + 1) [a.start]

/-- A test Adventure with many paths: Scene `i` leads to Scenes `i + 1` and `i + 2`, for 20 Scenes.
Each Scene can be reached in many ways. -/
private def manyPaths : Adventure where
  title := "Many paths"
  start := 0
  scenes := (List.range 20).map fun i =>
    { id := i, title := "", text := "",
      choices := if i + 2 < 20 then [{ text := "a", outcome := .goto (i + 1) },
                                     { text := "b", outcome := .goto (i + 2) }] else [] }

-- The search lists each Scene once, so its size stays at the number of Scenes.
#guard (reachableScenes manyPaths).length == 20

/-- Every Scene in `reachableScenes a` can be reached from the start. -/
theorem reachable_of_mem {a : Adventure} {x : SceneId}
    (h : x ∈ reachableScenes a) : Reachable a x := by
  apply explore_reachable _ [a.start] _ x h
  intro y hy
  simp only [List.mem_singleton] at hy
  subst hy
  exact Reachable.start

/-! ## A way to an Ending -/

/-- The numbers of the Endings: the Scenes with no Choices. -/
def endings (a : Adventure) : List SceneId :=
  (a.scenes.filter (·.choices.isEmpty)).map (·.id)

/-- Each Scene in `endings a` is an Ending. -/
theorem isEnding_of_mem_endings {a : Adventure} {s : SceneId}
    (h : s ∈ endings a) : IsEnding a s := by
  simp only [endings, List.mem_map, List.mem_filter, List.isEmpty_iff] at h
  obtain ⟨sc, ⟨hsc, hnil⟩, hid⟩ := h
  exact ⟨sc, hsc, hid, hnil⟩

/-- Backward expansion finds scenes with an edge into the set already found. -/
def exploreBack (a : Adventure) : Nat → List SceneId → List SceneId :=
  exploreClosure (fun found => (a.scenes.map (·.id)).filter fun s =>
    (successors a s).any (· ∈ found))

theorem exploreBack_reachesEnding {a : Adventure} (fuel : Nat) (found : List SceneId)
    (h : ∀ x ∈ found, ReachesEnding a x) : ∀ x ∈ exploreBack a fuel found, ReachesEnding a x := by
  apply exploreClosure_invariant _ _ _ fuel found h
  intro found hs x hx
  simp only [List.mem_filter, List.any_eq_true, decide_eq_true_eq] at hx
  obtain ⟨_, t, hedge, hfound⟩ := hx
  exact ReachesEnding.next (leads_of_mem_successors hedge) (hs t hfound)

/-- The Scenes from which the checker finds a way to an Ending. -/
def endingScenes (a : Adventure) : List SceneId :=
  exploreBack a (a.scenes.length + 1) (endings a)

/-- From every Scene in `endingScenes a`, an Ending can be reached. -/
theorem reachesEnding_of_mem {a : Adventure} {x : SceneId}
    (h : x ∈ endingScenes a) : ReachesEnding a x := by
  apply exploreBack_reachesEnding _ (endings a) _ x h
  intro y hy
  exact ReachesEnding.ending (isEnding_of_mem_endings hy)

/-- All errors in an Adventure, for the Character `c`. Each error names its Scene. -/
def check (rules : RuleSet) (c : Being) (a : Adventure) : List String :=
  -- Each search runs once, not once for each Scene.
  let reach := reachableScenes a
  let ends := endingScenes a
  need (SceneExists a a.start) s!"the start Scene {a.start} does not exist" ++
  need (a.scenes.map (·.id)).Nodup "two Scenes share a number" ++
  need (∃ s ∈ a.scenes, s.choices = []) "no Scene is an Ending" ++
  a.scenes.flatMap (fun s =>
    s.choices.flatMap (fun ch =>
      (checkOutcome rules c a ch.outcome).map (fun e => s!"Scene {s.id} ({s.title}), choice \"{ch.text}\": {e}"))) ++
  a.scenes.flatMap (fun s =>
    need (s.id ∈ reach) s!"Scene {s.id} ({s.title}) cannot be reached from the start") ++
  a.scenes.flatMap (fun s =>
    need (s.id ∈ ends)
      s!"Scene {s.id} ({s.title}) has no way to an Ending: no path of Choices from it leads to a Scene with no Choices")

/-- **The checker is sound.** If `check` finds no errors, the Adventure is legal by the spec. -/
theorem check_sound {rules : RuleSet} {c : Being} {a : Adventure}
    (h : check rules c a = []) : LegalAdventure rules c a := by
  simp only [check, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨hStart, hNodup⟩, _hEnding⟩, hScenes⟩, hReach⟩, hEnd⟩ := h
  refine ⟨need_sound hStart, need_sound hNodup, ?_, ?_, ?_⟩
  -- Every Choice is legal.
  · intro s hs ch hch
    exact checkOutcome_sound (hScenes s hs ch hch)
  -- Every Scene can be reached.
  · intro s hs
    exact reachable_of_mem (need_sound (hReach s hs))
  -- From every Scene, an Ending can be reached.
  · intro s hs
    exact reachesEnding_of_mem (need_sound (hEnd s hs))

end Rpg
