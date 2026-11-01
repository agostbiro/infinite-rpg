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

instance (rules : RuleSet) (c : Being) (a : Adventure) (o : Outcome) : Decidable (LegalOutcome rules c a o) := by
  unfold LegalOutcome; cases o <;> infer_instance

/-- No error if `p` is true, else one error with the message `msg`. -/
def need (p : Prop) [Decidable p] (msg : String) : List String :=
  if p then [] else [msg]

/-- If `need p msg` gives no error, then `p` is true. -/
theorem need_sound {p : Prop} [Decidable p] {msg : String}
    (h : need p msg = []) : p := by
  unfold need at h
  split at h
  · assumption
  · simp at h

/-- Errors in the skills of a being. -/
def checkSkills (rules : RuleSet) (b : Being) : List String :=
  need (∀ e ∈ b.skills, (rules.skillStep b e.1 e.2).isSome)
    s!"{b.name}: a skill level is too low to buy" ++
  need (b.skills.map (·.1)).Nodup
    s!"{b.name}: a skill is listed twice"

/-- If `checkSkills rules` finds no errors, the skills are bought correctly. -/
theorem checkSkills_sound {rules : RuleSet} {b : Being}
    (h : checkSkills rules b = []) : SkillsWellBought rules b := by
  simp only [checkSkills, List.append_eq_nil_iff] at h
  exact ⟨need_sound h.1, need_sound h.2⟩

/-- Errors in the build of a Creature. -/
def checkCreature (rules : RuleSet) (b : Being) : List String :=
  need (∀ a ∈ [b.st, b.dx, b.iq, b.ht], rules.creatureAttributeMin ≤ a ∧ a ≤ rules.creatureAttributeMax)
    s!"{b.name}: each attribute must be from {rules.creatureAttributeMin} to {rules.creatureAttributeMax}" ++
  need (rules.points b ≤ rules.creaturePointLimit)
    s!"{b.name}: costs {rules.points b} points, but the limit is {rules.creaturePointLimit}" ++
  checkSkills rules b ++
  need (rules.minST b.weapon ≤ b.st)
    s!"{b.name}: ST {b.st} is too low for a {b.weapon.name} (needs {rules.minST b.weapon})"

/-- If `checkCreature rules` finds no errors, the Creature is a legal build. -/
theorem checkCreature_sound {rules : RuleSet} {b : Being}
    (h : checkCreature rules b = []) : LegalCreature rules b := by
  simp only [checkCreature, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨need_sound h1, need_sound h2, checkSkills_sound h3, need_sound h4⟩

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
    s!"{c.name}: natural DR exceeds {rules.characterNaturalDRLimit}"

/-- If `checkCharacter rules` finds no errors, the Character is a legal build. -/
theorem checkCharacter_sound {rules : RuleSet} {c : Being}
    (h : checkCharacter rules c = []) : LegalCharacter rules c := by
  simp only [checkCharacter, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨need_sound h1, need_sound h2, checkSkills_sound h3, need_sound h4, need_sound h5⟩

/-- Errors in the modifier of a Success Roll. -/
def checkModifier (rules : RuleSet) : Outcome → List String
  | .roll _ m _ _ => need (rules.modifierMin ≤ m ∧ m ≤ rules.modifierMax) s!"roll modifier {m} is not from {rules.modifierMin} to {rules.modifierMax}"
  | _ => []

/-- Errors in the list of Creatures in a Fight. -/
def checkFoesNonempty : Outcome → List String
  | .fight fs _ => need (fs ≠ []) "a Fight has no Creatures"
  | _ => []

/-- Errors in one Creature of a Fight against the Character `c`. -/
def checkFoe (rules : RuleSet) (c f : Being) : List String :=
  checkCreature rules f ++
  need (FightCanEnd rules c f)
    s!"{f.name}: neither side has an attack that can injure the other under this adventure’s rules"

/-- Errors in the Outcome of a Choice. -/
def checkOutcome (rules : RuleSet) (c : Being) (a : Adventure) (o : Outcome) : List String :=
  o.targets.flatMap (fun t => need (SceneExists a t) s!"Scene {t} does not exist") ++
  checkModifier rules o ++
  checkFoesNonempty o ++
  o.foes.flatMap (checkFoe rules c)

/-- If `checkOutcome rules` finds no errors, the Outcome is legal. -/
theorem checkOutcome_sound {rules : RuleSet} {c : Being} {a : Adventure} {o : Outcome}
    (h : checkOutcome rules c a o = []) : LegalOutcome rules c a o := by
  simp only [checkOutcome, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  obtain ⟨⟨⟨hTargets, hMod⟩, hFoes⟩, hEach⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Every target Scene exists.
  · intro t ht
    exact need_sound (hTargets t ht)
  -- The roll modifier is in range.
  · cases o <;> first | trivial | exact need_sound hMod
  -- A Fight has at least one Creature.
  · cases o <;> first | trivial | exact need_sound hFoes
  -- Each Creature is legal and its Fight can end.
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

/-- Search from the Scenes in `seen`, for at most `fuel` steps.
Returns `seen` plus every Scene found. -/
def explore (a : Adventure) : Nat → List SceneId → List SceneId
  | 0, seen => seen
  | fuel + 1, seen =>
    let found := (seen.flatMap (successors a)).filter (· ∉ seen)
    if found = [] then seen else explore a fuel (seen ++ found)

/-- If every Scene in `seen` can be reached, so can every Scene that `explore` returns. -/
theorem explore_reachable {a : Adventure} :
    ∀ (fuel : Nat) (seen : List SceneId),
    (∀ x ∈ seen, Reachable a x) → ∀ x ∈ explore a fuel seen, Reachable a x := by
  intro fuel
  induction fuel with
  -- No fuel: `explore` returns `seen`.
  | zero =>
    intro seen h
    simpa [explore] using h
  -- One more step: each Scene found is a successor of a Scene in `seen`.
  | succ n ih =>
    intro seen h
    simp only [explore]
    split
    · exact h
    · apply ih
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · simp only [List.mem_filter, List.mem_flatMap] at hx
        obtain ⟨⟨s, hs, hsucc⟩, _⟩ := hx
        exact Reachable.next (h s hs) (leads_of_mem_successors hsucc)

/-- The Scenes that the checker finds can be reached from the start. -/
def reachableScenes (a : Adventure) : List SceneId :=
  explore a (a.scenes.length + 1) [a.start]

/-- Every Scene in `reachableScenes a` can be reached from the start. -/
theorem reachable_of_mem {a : Adventure} {x : SceneId}
    (h : x ∈ reachableScenes a) : Reachable a x := by
  apply explore_reachable _ [a.start] _ x h
  intro y hy
  simp only [List.mem_singleton] at hy
  subst hy
  exact Reachable.start

/-- All errors in an Adventure, for the Character `c`. Each error names its Scene. -/
def check (rules : RuleSet) (c : Being) (a : Adventure) : List String :=
  need (SceneExists a a.start) s!"the start Scene {a.start} does not exist" ++
  need (a.scenes.map (·.id)).Nodup "two Scenes share a number" ++
  need (∃ s ∈ a.scenes, s.choices = []) "no Scene is an Ending" ++
  a.scenes.flatMap (fun s =>
    s.choices.flatMap (fun ch =>
      (checkOutcome rules c a ch.outcome).map (fun e => s!"Scene {s.id} ({s.title}), choice \"{ch.text}\": {e}"))) ++
  a.scenes.flatMap (fun s =>
    need (s.id ∈ reachableScenes a) s!"Scene {s.id} ({s.title}) cannot be reached from the start")

/-- **The checker is sound.** If `check rules` finds no errors, the Adventure is legal by the spec. -/
theorem check_sound {rules : RuleSet} {c : Being} {a : Adventure}
    (h : check rules c a = []) : LegalAdventure rules c a := by
  simp only [check, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨hStart, hNodup⟩, hEnding⟩, hScenes⟩, hReach⟩ := h
  refine ⟨need_sound hStart, need_sound hNodup, need_sound hEnding, ?_, ?_⟩
  -- Every Choice is legal.
  · intro s hs ch hch
    exact checkOutcome_sound (hScenes s hs ch hch)
  -- Every Scene can be reached.
  · intro s hs
    exact reachable_of_mem (need_sound (hReach s hs))

end Rpg
