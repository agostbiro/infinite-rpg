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

instance (b : Being) : Decidable (SkillsWellBought b) := by
  unfold SkillsWellBought; infer_instance

instance (b : Being) : Decidable (LegalCreature b) := by
  unfold LegalCreature; infer_instance

instance (c : Being) : Decidable (LegalCharacter c) := by
  unfold LegalCharacter; infer_instance

instance (c : Being) (a : Adventure) (o : Outcome) : Decidable (LegalOutcome c a o) := by
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
def checkSkills (b : Being) : List String :=
  need (∀ e ∈ b.skills, (b.skillStep e.1 e.2).isSome)
    s!"{b.name}: a skill level is too low to buy" ++
  need (b.skills.map (·.1)).Nodup
    s!"{b.name}: a skill is listed twice"

/-- If `checkSkills` finds no errors, the skills are bought correctly. -/
theorem checkSkills_sound {b : Being}
    (h : checkSkills b = []) : SkillsWellBought b := by
  simp only [checkSkills, List.append_eq_nil_iff] at h
  exact ⟨need_sound h.1, need_sound h.2⟩

/-- Errors in the build of a Creature. -/
def checkCreature (b : Being) : List String :=
  need (∀ a ∈ [b.st, b.dx, b.iq, b.ht], 1 ≤ a ∧ a ≤ 20)
    s!"{b.name}: each attribute must be from 1 to 20" ++
  need (b.points ≤ 150)
    s!"{b.name}: costs {b.points} points, but the limit is 150" ++
  checkSkills b ++
  need (b.weapon.minST ≤ b.st)
    s!"{b.name}: ST {b.st} is too low for a {b.weapon.name} (needs {b.weapon.minST})"

/-- If `checkCreature` finds no errors, the Creature is a legal build. -/
theorem checkCreature_sound {b : Being}
    (h : checkCreature b = []) : LegalCreature b := by
  simp only [checkCreature, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨need_sound h1, need_sound h2, checkSkills_sound h3, need_sound h4⟩

/-- Errors in the build of the Character. -/
def checkCharacter (c : Being) : List String :=
  need (∀ a ∈ [c.st, c.dx, c.iq, c.ht], 7 ≤ a ∧ a ≤ 14)
    s!"{c.name}: each attribute must be from 7 to 14" ++
  need (c.points = 100)
    s!"{c.name}: costs {c.points} points, but must cost exactly 100" ++
  checkSkills c ++
  need (c.weapon.minST ≤ c.st)
    s!"{c.name}: ST {c.st} is too low for a {c.weapon.name} (needs {c.weapon.minST})" ++
  need (c.naturalDR = 0)
    s!"{c.name}: the Character cannot have natural DR"

/-- If `checkCharacter` finds no errors, the Character is a legal build. -/
theorem checkCharacter_sound {c : Being}
    (h : checkCharacter c = []) : LegalCharacter c := by
  simp only [checkCharacter, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨need_sound h1, need_sound h2, checkSkills_sound h3, need_sound h4, need_sound h5⟩

/-- Errors in the modifier of a Success Roll. -/
def checkModifier : Outcome → List String
  | .roll _ m _ _ => need (-10 ≤ m ∧ m ≤ 10) s!"roll modifier {m} is not from -10 to +10"
  | _ => []

/-- Errors in a Success Roll that the Character `c` cannot try. -/
def checkCanTry (c : Being) : Outcome → List String
  | .roll t m _ _ =>
    need (CanTryRoll c t m)
      s!"{c.name} cannot try this {t.name} roll at {m}: the effective skill must be 3 or more"
  | _ => []

/-- Errors in the list of Creatures in a Fight. -/
def checkFoesNonempty : Outcome → List String
  | .fight fs _ => need (fs ≠ []) "a Fight has no Creatures"
  | _ => []

/-- Errors in one Creature of a Fight against the Character `c`. -/
def checkFoe (c f : Being) : List String :=
  checkCreature f ++
  need (FightCanEnd c f)
    s!"{f.name}: the Fight can never end, because neither side can hurt the other (attack skill below 3, or no hit can get past DR)"

/-- Errors in the Outcome of a Choice. -/
def checkOutcome (c : Being) (a : Adventure) (o : Outcome) : List String :=
  o.targets.flatMap (fun t => need (SceneExists a t) s!"Scene {t} does not exist") ++
  checkModifier o ++
  checkCanTry c o ++
  checkFoesNonempty o ++
  o.foes.flatMap (checkFoe c)

/-- If `checkOutcome` finds no errors, the Outcome is legal. -/
theorem checkOutcome_sound {c : Being} {a : Adventure} {o : Outcome}
    (h : checkOutcome c a o = []) : LegalOutcome c a o := by
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

/-- Search back from the Scenes in `found`, for at most `fuel` steps. Each step adds every Scene
with a Choice that leads into `found`. Returns `found` plus every Scene added. -/
def exploreBack (a : Adventure) : Nat → List SceneId → List SceneId
  | 0, found => found
  | fuel + 1, found =>
    let more := (a.scenes.map (·.id)).filter fun s =>
      s ∉ found ∧ (successors a s).any (· ∈ found)
    if more = [] then found else exploreBack a fuel (found ++ more)

/-- If an Ending can be reached from every Scene in `found`, the same is true for every Scene
that `exploreBack` returns. -/
theorem exploreBack_reachesEnding {a : Adventure} :
    ∀ (fuel : Nat) (found : List SceneId),
    (∀ x ∈ found, ReachesEnding a x) → ∀ x ∈ exploreBack a fuel found, ReachesEnding a x := by
  intro fuel
  induction fuel with
  -- No fuel: `exploreBack` returns `found`.
  | zero =>
    intro found h
    simpa [exploreBack] using h
  -- One more step: each Scene added has a Choice that leads into `found`.
  | succ n ih =>
    intro found h
    simp only [exploreBack]
    split
    · exact h
    · apply ih
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · simp only [List.mem_filter, List.any_eq_true, decide_eq_true_eq] at hx
        obtain ⟨_, _, t, ht, hfound⟩ := hx
        exact ReachesEnding.next (leads_of_mem_successors ht) (h t hfound)

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
def check (c : Being) (a : Adventure) : List String :=
  need (SceneExists a a.start) s!"the start Scene {a.start} does not exist" ++
  need (a.scenes.map (·.id)).Nodup "two Scenes share a number" ++
  need (∃ s ∈ a.scenes, s.choices = []) "no Scene is an Ending" ++
  a.scenes.flatMap (fun s =>
    s.choices.flatMap (fun ch =>
      (checkOutcome c a ch.outcome).map (fun e => s!"Scene {s.id} ({s.title}), choice \"{ch.text}\": {e}"))) ++
  a.scenes.flatMap (fun s =>
    need (s.id ∈ reachableScenes a) s!"Scene {s.id} ({s.title}) cannot be reached from the start") ++
  a.scenes.flatMap (fun s =>
    need (s.id ∈ endingScenes a)
      s!"Scene {s.id} ({s.title}) has no way to an Ending: no path of Choices from it leads to a Scene with no Choices")

/-- **The checker is sound.** If `check` finds no errors, the Adventure is legal by the spec. -/
theorem check_sound {c : Being} {a : Adventure}
    (h : check c a = []) : LegalAdventure c a := by
  simp only [check, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨hStart, hNodup⟩, hEnding⟩, hScenes⟩, hReach⟩, hEnd⟩ := h
  refine ⟨need_sound hStart, need_sound hNodup, need_sound hEnding, ?_, ?_, ?_⟩
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
