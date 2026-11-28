import Rpg.Probability.RoundRefinement
import Std.Data.HashSet.Basic

/-!
# A faster exact round

`roundDistribution` (in `Combat.lean`) is the exact round that the combat theorems are about.
It runs the Engine's `attackWith` on every sum of the dice, so one attack walks about 2,000 dice
paths and builds the Reports of each path. This file gives a faster round with the same odds.

* `injuryDistribution` computes the injury of one attack from a few small tables. It groups the
  attack rolls by result, it rolls the Dodge once, and it rolls the damage once.
* `fastRound` is `roundDistribution` with this attack in place of `attackDistribution`, and with
  `sortCollect` in place of `collect`. `sortCollect` sorts the states before it merges them.
* `fastRound_expect`: for every observable of the state after the round, `fastRound` and
  `roundDistribution` give the same expected value.

`StoppingProcess.SameOdds` (`Stopping.lean`) then carries each fact about a process with these
rounds to `combatProcess` (`CombatCertificate.lean`).

The two rounds can list their results in a different order, or merge them differently. Only the
expected values must agree, and the theorems check exactly that.
-/
namespace Rpg.Probability

/-- The sum of three fair dice. It is a top-level value, so compiled code computes it once. -/
def threeDice : Distribution Nat := dice 3

/-- One more fair die added to the sum `d`. -/
def addDie (d : Distribution Nat) : Distribution Nat :=
  (do
    let a ← uniform [1, 2, 3, 4, 5, 6]
    let b ← d
    pure (a + b)).collect

/-- The sum of `n` fair dice, as `dice` gives it. It computes the sum of one die fewer once, not
once for each face of the new die. -/
def sharedDice : Nat → Distribution Nat
  | 0 => pure 0
  | n + 1 => addDie (sharedDice n)

/-- `sharedDice` is `dice`. -/
theorem sharedDice_eq (n : Nat) : sharedDice n = dice n := by
  induction n with
  -- No dice: both sums are 0.
  | zero => rfl
  -- One more die: both add one die to the same sum.
  | succ n ih => simp only [sharedDice, ih, addDie, dice]

/-- The sums of 0 to 12 fair dice. It is a top-level value, so compiled code computes it once. -/
def damageSumTable : Array (Distribution Nat) := Array.ofFn (n := 13) fun i => sharedDice i

/-- The sum of `n` fair dice: from `damageSumTable` for at most 12 dice, else from `sharedDice`. -/
def damageSums (n : Nat) : Distribution Nat :=
  if h : n < damageSumTable.size then damageSumTable[n] else sharedDice n

/-- `damageSums` is `dice`. -/
theorem damageSums_eq (n : Nat) : damageSums n = dice n := by
  unfold damageSums
  split
  -- At most 12 dice: the table entry is `sharedDice n`.
  · simp [damageSumTable, sharedDice_eq]
  -- More dice: `sharedDice n` itself.
  · exact sharedDice_eq n

/-- The exact injury of one attack by `att` on `dfn`, as in `attackWith` with fair dice.
The attack roll is grouped by its result and by whether it is a 3. The Dodge roll and the damage
roll are each computed once, and the sums of the damage dice come from `damageSums`. -/
def injuryDistribution (rules : RuleSet) (attId : Actor) (att : Fighter) (dfnId : Actor)
    (dfn : Fighter) : Distribution Nat :=
  let offense := rules.combatRules.filter fun r => r.active rules attId att dfn &&
    (r.hitBonus != 0 || r.damageBonus != 0)
  let defense := rules.combatRules.filter fun r => r.active rules dfnId dfn att && r.armorBonus > 0
  let level := rules.weaponLevel attId.isNone att.being + att.maneuver.hitBonus +
    (offense.map (·.hitBonus)).sum
  if level < rules.minimumRollLevel then pure 0 else
  let baseDice := rules.weaponDice attId.isNone att.being
  let damageDice : Dice := { baseDice with add := baseDice.add + (offense.map (·.damageBonus)).sum }
  let kind := att.being.weapon.damageType
  let dr := rules.dr dfn.being + (defense.map (·.armorBonus)).sum
  let injuryOf (sum : Nat) : Nat := rules.injury kind dr (rules.basicDamage damageDice kind sum)
  -- The rolled damage is computed only if a hit needs it, and then once for all such hits.
  let rolled : Thunk (Distribution Nat) :=
    Thunk.mk fun _ => (injuryOf <$> damageSums damageDice.count).collect
  let maxed : Nat := injuryOf (List.replicate damageDice.count 6).sum
  let dodged : Distribution Bool := match dfn.dodge rules with
    | none => pure false
    | some d => ((fun t => (rules.successRoll d t).succeeded) <$> threeDice).collect
  -- `damage` is a function, so a miss does not force the rolled damage.
  let onHit (result : RollResult) (top : Bool) : Distribution Nat :=
    let damage (_ : Unit) := if top then pure maxed else rolled.get
    if !result.succeeded then pure 0
    else if result = .criticalSuccess then damage ()
    else dodged.bind fun d => if d then pure 0 else damage ()
  let classes := ((fun t => (rules.successRoll level t, t == 3)) <$> threeDice).collect
  (classes.bind fun c => onHit c.1 c.2).collect

/-- The attack of `injuryDistribution`, with no Reports. -/
def fastAttack (rules : RuleSet) : AttackFn Distribution :=
  fun attId att dfnId dfn =>
    (fun inj => (inj, ([] : List Report))) <$> injuryDistribution rules attId att dfnId dfn

/-! ## Merging equal states quickly -/

/-- Go through `xs` and merge each entry into the entry before it when they hold the same value.
`done` holds the merged entries so far, last first. The function calls itself only as its last
step, so it needs no stack for a long list. -/
def mergeAdjacentInto [DecidableEq α] : List (α × Rat) → List (α × Rat) → List (α × Rat)
  | done, [] => done.reverse
  | (y, q) :: done, (x, p) :: rest =>
    if x = y then mergeAdjacentInto ((y, q + p) :: done) rest
    else mergeAdjacentInto ((x, p) :: (y, q) :: done) rest
  | [], (x, p) :: rest => mergeAdjacentInto [(x, p)] rest

/-- Merge each entry into the entry before it when they hold the same value. In a sorted list,
equal values are next to each other, so this merges all of them. -/
def mergeAdjacent [DecidableEq α] (xs : List (α × Rat)) : List (α × Rat) :=
  mergeAdjacentInto [] xs

/-- Merge equal values, as `collect` does, but sort the entries by `key` first and then merge
neighbours, so that it does not compare every pair. A `key` that gives two values the same
number can leave some equal values unmerged, but it never merges two different values. -/
def Distribution.sortCollect [DecidableEq α] (key : α → Nat) (d : Distribution α) :
    Distribution α :=
  let keyed := d.entries.map fun e => (key e.1, e)
  ⟨mergeAdjacent ((keyed.mergeSort fun a b => decide (a.1 ≤ b.1)).map Prod.snd)⟩

/-! ## The fast round -/

/-- The Creature turns in `actors` with `fastAttack`, with equal states merged after each turn.
It is `foesDistribution` with `fastAttack`. -/
def fastFoes (rules : RuleSet) : FightState → List Actor → Distribution FightState
  | s, [] => pure s
  | s, a :: rest =>
    (((Prod.fst <$> foeTurnsWith (fastAttack rules) s [a]).sortCollect stateKey).bind
      fun s => fastFoes rules s rest).sortCollect stateKey

/-- One round in turn order `order`, with `heroPolicy` and `fastAttack`. It is
`roundDistribution` with `fastAttack`, and with `sortCollect` in place of `collect`. -/
def fastRound (rules : RuleSet) (order : List Actor) (s : FightState) : Distribution FightState :=
  let before := fastFoes rules s (beforeCharacter order)
  let mine := (before.bind fun s =>
    if s.over then pure s
    else (heroPolicy s).bind fun (m, t) =>
      Prod.fst <$> heroTurnWith (fastAttack rules) s m t).sortCollect stateKey
  (mine.bind fun s => fastFoes rules s (afterCharacter order)).sortCollect stateKey

/-- The damage bonus and the DR of one attack by `att` on `dfn`, as `injuryDistribution` computes
them. They are the only parts of the attack that change which injuries it can give. -/
def injuryTerms (rules : RuleSet) (attId : Actor) (att : Fighter) (dfnId : Actor)
    (dfn : Fighter) : Int × Nat :=
  let offense := rules.combatRules.filter fun r => r.active rules attId att dfn &&
    (r.hitBonus != 0 || r.damageBonus != 0)
  let defense := rules.combatRules.filter fun r => r.active rules dfnId dfn att && r.armorBonus > 0
  ((offense.map (·.damageBonus)).sum, rules.dr dfn.being + (defense.map (·.armorBonus)).sum)

/-- The number of different injuries that an attack by `att` with damage bonus `bonus` against
DR `dr` can give. Each injury is 0 or the injury of one sum of the damage dice, so this is an upper
bound on the results of `injuryDistribution`, which merges equal injuries. A hash set counts them,
so the time grows linearly with the number of dice. -/
def injuryCount (rules : RuleSet) (attId : Actor) (att : Fighter) (bonus : Int) (dr : Nat) :
    Nat :=
  let baseDice := rules.weaponDice attId.isNone att.being
  let damageDice : Dice := { baseDice with add := baseDice.add + bonus }
  let kind := att.being.weapon.damageType
  let injuries := (List.range (5 * damageDice.count + 1)).map fun k =>
    rules.injury kind dr (rules.basicDamage damageDice kind (damageDice.count + k))
  (injuries.foldl (fun seen i => seen.insert i) (({} : Std.HashSet Nat).insert 0)).size

/-- The HP values from 1 to `limit` that `maxInjuries` tries for `being`: the least HP in each
case of the HP triggers. The cases are: at most one third of full HP, at most one half, and more
than one half. -/
def hpSamples (rules : RuleSet) (being : Being) (limit : Nat) : List Nat :=
  let full := rules.maxHP being
  ([1, full / 3 + 1, full / 2 + 1].filter (· ≤ limit)).eraseDups

/-- An upper bound on the injury results of one attack of `att` on `dfn`, over every HP from 1 to
`attHP` and `dfnHP` and every maneuver of the two. A combat rule reads HP only through the
`wounded` and `desperate` triggers, so it tries only the HP values of `hpSamples`. It counts
injuries once for each different damage bonus and DR, so it does not compute any attack. -/
def maxInjuries (rules : RuleSet) (a : Actor) (att : Fighter) (attHP : Nat) (b : Actor)
    (dfn : Fighter) (dfnHP : Nat) : Nat :=
  let add (seen : List (Int × Nat)) (i : Nat) (m : Maneuver) (j : Nat) (n : Maneuver) :=
    let t := injuryTerms rules a {att with hp := i, maneuver := m} b
      {dfn with hp := j, maneuver := n}
    if seen.contains t then seen else t :: seen
  let terms := (hpSamples rules att.being attHP).foldl (fun seen i => maneuverMenu.foldl
    (fun seen m => (hpSamples rules dfn.being dfnHP).foldl (fun seen j => maneuverMenu.foldl
      (fun seen n => add seen i m j n) seen) seen) seen) []
  terms.foldl (fun best (bonus, dr) => max best (injuryCount rules a att bonus dr)) 1

/-- For each Creature of a Fight, an upper bound on the injury results of one attack by the
Character on it (`heroHits`) and by it on the Character (`foeHits`), from `maxInjuries`. -/
structure AttackBounds where
  /-- The bound for an attack by the Character on each Creature, by number. -/
  heroHits : List Nat
  /-- The bound for an attack by each Creature on the Character, by number. -/
  foeHits : List Nat

/-- The attack bounds of the Fight that `s` is in. HP never goes up in a Fight, so each Fighter's
HP stays at most its full HP or its HP in `s`, whichever is larger. -/
def attackBounds (rules : RuleSet) (s : FightState) : AttackBounds :=
  let limit (f : Fighter) : Nat := max (rules.maxHP f.being) f.hp.toNat
  let pairs := s.foes.zipIdx.map fun (f, i) =>
    (maxInjuries rules none s.hero (limit s.hero) (some i) f (limit f),
     maxInjuries rules (some i) f (limit f) none s.hero (limit s.hero))
  {heroHits := pairs.map Prod.fst, foeHits := pairs.map Prod.snd}

/-- An upper bound on the number of results that `fastRound` makes from `s` if it merges none.
It holds if `bounds` is from `attackBounds`, the combat rules read only HP and maneuvers, and
`order` names each Creature once. Tests check it, and no proof uses it. -/
def roundSizeBound (order : List Actor) (bounds : AttackBounds) (s : FightState) : Nat :=
  let living := s.livingFoes
  -- The Character's turn: one branch for each maneuver and target of `heroPolicy`.
  let heroBranch (m : Maneuver) (t : Nat) : Nat :=
    if !m.attacks then 1
    else if s.hero.being.weapon.spray then
      living.foldl (fun acc i => acc * bounds.heroHits.getD i 1) 1
    else bounds.heroHits.getD t 1
  let heroPart := ((heroPolicy s).entries.map fun ((m, t), _) => heroBranch m t).sum
  -- The turns of the living Creatures: each one multiplies the results by its injuries, at most.
  let foePart := (order.filterMap id).foldl (fun acc i =>
    if i ∈ living then acc * bounds.foeHits.getD i 1 else acc) 1
  max 1 heroPart * foePart

/-- The solver as the combat check runs it: `fastRound`, with each round bounded by
`roundSizeBound` with the attack bounds of the Fight, within `budget`. It also says why the solver
stopped. -/
def solveCheckedReport (rules : RuleSet) (order : List Actor) (bounds : AttackBounds)
    (starts : List FightState) (budget : SolveBudget := {}) : SolveReport :=
  solveFightReport (fastRound rules order) starts (roundSizeBound order bounds) budget

/-- The answers of `solveCheckedReport`, without the reason why the solver stopped. -/
def solveChecked (rules : RuleSet) (order : List Actor) (bounds : AttackBounds)
    (starts : List FightState) (budget : SolveBudget := {}) : CombatCache :=
  (solveCheckedReport rules order bounds starts budget).cache

/-- One round of the fast process. An ended Fight stays as it is. -/
def fastStep (rules : RuleSet) (order : List Actor) (s : FightState) : Distribution FightState :=
  if s.over then pure s else fastRound rules order s

/-! ## The fast attack has the odds of `attackDistribution` -/

attribute [local simp] Distribution.expect_ite

/-- For every observable of the injury, `injuryDistribution` and `attackDistribution` give the
same expected value. -/
theorem injuryDistribution_expect (rules : RuleSet) (a : Actor) (att : Fighter) (b : Actor)
    (dfn : Fighter) (g : Nat → Rat) :
    (injuryDistribution rules a att b dfn).expect g =
      (attackDistribution rules a att b dfn).expect (fun r => g r.1) := by
  -- Both sides become sums over the sum of three dice, one case for each Dodge score.
  -- The proof needs the two sums to unfold to the same terms, so a change to the simp set or
  -- to the toolchain can break it.
  cases h : dfn.dodge rules <;>
    simp [injuryDistribution, attackDistribution, attackWith, rollAgainstWith, damageFacesWith,
      Bind.bind, Distribution.expect_bind, sumAsFaces, threeDice, damageSums_eq, Thunk.get, h]
  -- Split on whether the attack level is too low to roll.
  all_goals split
  -- Too low: both sides give no injury.
  all_goals try rfl
  -- High enough: the sums over the dice agree term by term.
  all_goals congr 1

/-- The injury of one attack is a probability distribution. -/
theorem injuryDistribution_valid (rules : RuleSet) (a : Actor) (att : Fighter) (b : Actor)
    (dfn : Fighter) : (injuryDistribution rules a att b dfn).Valid := by
  simp only [injuryDistribution, threeDice, damageSums_eq, Thunk.get]
  repeat first
    | exact Distribution.valid_pure _
    | exact dice_valid _
    | apply Distribution.valid_collect
    | apply Distribution.valid_map
    | apply Distribution.valid_bind
    | split
    | intro

/-- `fastAttack` is `attackDistribution`, up to the order and merging of its entries. -/
theorem fastAttack_forgets (rules : RuleSet) :
    ForgetsReports (fastAttack rules) (attackDistribution rules) := by
  intro a att b dfn observe
  simp only [fastAttack, Distribution.expect_map]
  exact injuryDistribution_expect rules a att b dfn (fun inj => observe (inj, []))

/-- The fast attack is a probability distribution. -/
theorem fastAttack_valid (rules : RuleSet) (a : Actor) (att : Fighter) (b : Actor)
    (dfn : Fighter) : (fastAttack rules a att b dfn).Valid :=
  Distribution.valid_map _ _ (injuryDistribution_valid rules a att b dfn)

/-! ## Sorting and merging keeps the odds -/

/-- Reordering the entries does not change an expected value. -/
theorem weightedSum_perm {xs ys : List (α × Rat)} (h : xs.Perm ys) (f : α → Rat) :
    weightedSum xs f = weightedSum ys f := by
  induction h with
  -- Two empty lists.
  | nil => rfl
  -- The same first entry.
  | cons e _ ih =>
    rcases e with ⟨x, p⟩
    simp [ih]
  -- The first two entries change places.
  | swap e e' _ =>
    rcases e with ⟨x, p⟩
    rcases e' with ⟨y, q⟩
    simp
    grind
  -- Two reorderings, one after the other.
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Merging neighbours does not change an expected value: the result has the expected value of
`done` and `xs` together. -/
theorem weightedSum_mergeAdjacentInto [DecidableEq α] (done xs : List (α × Rat)) (f : α → Rat) :
    weightedSum (mergeAdjacentInto done xs) f = weightedSum done f + weightedSum xs f := by
  induction xs generalizing done with
  -- No entries are left: the merged entries are put back in order.
  | nil =>
    simp only [mergeAdjacentInto, weightedSum_nil, Rat.add_zero]
    exact weightedSum_perm (List.reverse_perm done) f
  -- Entry `e` is merged into the last merged entry or put after it, then the rest follows.
  | cons e rest ih =>
    rcases e with ⟨x, p⟩
    cases done with
    -- Nothing is merged yet, so the entry starts the merged list.
    | nil =>
      simp only [mergeAdjacentInto, ih, weightedSum_cons, weightedSum_nil]
      grind
    -- Some entries are merged; `d` is the last one.
    | cons d done =>
      rcases d with ⟨y, q⟩
      simp only [mergeAdjacentInto]
      split
      -- The entry holds the value of the last merged entry, so the two weights are added.
      · next same =>
        subst same
        simp only [ih, weightedSum_cons]
        grind
      -- The entry holds a different value, so it starts a new merged entry.
      · simp only [ih, weightedSum_cons]
        grind

/-- Merging neighbours does not change an expected value. -/
theorem weightedSum_mergeAdjacent [DecidableEq α] (xs : List (α × Rat)) (f : α → Rat) :
    weightedSum (mergeAdjacent xs) f = weightedSum xs f := by
  simp [mergeAdjacent, weightedSum_mergeAdjacentInto, Rat.zero_add]

/-- Merging neighbours keeps every weight nonnegative. -/
theorem mergeAdjacentInto_nonnegative [DecidableEq α] (done xs : List (α × Rat))
    -- The merged entries so far have nonnegative weights.
    (hdone : ∀ e ∈ done, 0 ≤ e.2)
    -- The entries left have nonnegative weights.
    (hxs : ∀ e ∈ xs, 0 ≤ e.2) :
    ∀ e ∈ mergeAdjacentInto done xs, 0 ≤ e.2 := by
  induction xs generalizing done with
  -- No entries are left: the result is `done` in the other order.
  | nil =>
    intro e he
    simp only [mergeAdjacentInto, List.mem_reverse] at he
    exact hdone e he
  -- Entry `e` is merged into the last merged entry or put after it, then the rest follows.
  | cons e rest ih =>
    rcases e with ⟨x, p⟩
    have hp : 0 ≤ p := hxs (x, p) (by simp)
    have hrest : ∀ e ∈ rest, 0 ≤ e.2 := fun e he => hxs e (by simp [he])
    cases done with
    -- Nothing is merged yet.
    | nil =>
      apply ih _ _ hrest
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rw [he]
      exact hp
    -- Some entries are merged; `d` is the last one.
    | cons d done =>
      rcases d with ⟨y, q⟩
      have hq : 0 ≤ q := hdone (y, q) (by simp)
      have hold : ∀ e ∈ done, 0 ≤ e.2 := fun e he => hdone e (by simp [he])
      simp only [mergeAdjacentInto]
      split
      -- The two weights are added.
      · apply ih _ _ hrest
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        -- The merged entry: the sum of two nonnegative weights.
        · exact Rat.add_nonneg hq hp
        -- An older merged entry.
        · exact hold e he
      -- The entry starts a new merged entry.
      · apply ih _ _ hrest
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        -- The new entry.
        · exact hp
        -- The last merged entry.
        · exact hq
        -- An older merged entry.
        · exact hold e he

/-- Merging neighbours keeps every weight nonnegative. -/
theorem mergeAdjacent_nonnegative [DecidableEq α] (xs : List (α × Rat))
    (h : ∀ e ∈ xs, 0 ≤ e.2) : ∀ e ∈ mergeAdjacent xs, 0 ≤ e.2 :=
  mergeAdjacentInto_nonnegative [] xs (by simp) h

/-- The sorted entries, with their keys dropped, are the old entries in some order. -/
private theorem sorted_perm (key : α → Nat) (xs : List (α × Rat)) :
    (((xs.map fun e => (key e.1, e)).mergeSort fun a b => decide (a.1 ≤ b.1)).map Prod.snd).Perm
      xs := by
  have h := (List.mergeSort_perm (xs.map fun e => (key e.1, e))
    (fun a b => decide (a.1 ≤ b.1))).map Prod.snd
  simpa [List.map_map, Function.comp_def] using h

/-- `sortCollect` keeps every expected value, as `collect` does. -/
@[simp] theorem Distribution.expect_sortCollect [DecidableEq α] (key : α → Nat)
    (d : Distribution α) (f : α → Rat) : (d.sortCollect key).expect f = d.expect f := by
  simp only [Distribution.sortCollect, Distribution.expect]
  rw [weightedSum_mergeAdjacent]
  exact weightedSum_perm (sorted_perm key d.entries) f

/-- `sortCollect` keeps a probability distribution valid. -/
theorem Distribution.valid_sortCollect [DecidableEq α] (key : α → Nat) (d : Distribution α)
    (hd : d.Valid) : (d.sortCollect key).Valid := by
  constructor
  -- Each weight is not negative.
  · apply mergeAdjacent_nonnegative
    intro e he
    exact hd.1 e ((sorted_perm key d.entries).mem_iff.mp he)
  -- The weights add up to 1.
  · rw [← weightedSum_one]
    change (d.sortCollect key).expect (fun _ => 1) = 1
    rw [Distribution.expect_sortCollect]
    exact Distribution.expect_const d hd 1

/-! ## Validity with any valid attack -/

section
variable {A : AttackFn Distribution} (hA : ∀ a att b dfn, (A a att b dfn).Valid)
include hA

/-- A spray with a valid attack is a probability distribution. -/
theorem sprayWith_valid (att : Fighter) (i : Nat) (foes : List Fighter) :
    (sprayWith A att i foes).Valid := by
  induction foes generalizing i with
  -- No Creature is left to hit.
  | nil => exact Distribution.valid_pure _
  -- The first Creature, then the rest.
  | cons foe foes ih =>
    simp only [sprayWith, Bind.bind]
    repeat first
      | exact Distribution.valid_pure _
      | exact hA _ _ _ _
      | exact ih _
      | apply Distribution.valid_bind
      | split
      | intro

/-- The Character's turn with a valid attack is a probability distribution. -/
theorem heroTurnWith_valid (s : FightState) (m : Maneuver) (target : Nat) :
    (heroTurnWith A s m target).Valid := by
  simp only [heroTurnWith, Bind.bind]
  repeat first
    | exact Distribution.valid_pure _
    | exact hA _ _ _ _
    | exact sprayWith_valid hA _ _ _
    | apply Distribution.valid_bind
    | split
    | intro

/-- The turns of the Creatures with a valid attack are a probability distribution. -/
theorem foeTurnsWith_valid (s : FightState) (actors : List Actor) :
    (foeTurnsWith A s actors).Valid := by
  induction actors generalizing s with
  -- No turn is left.
  | nil => exact Distribution.valid_pure _
  -- One more turn is in the list.
  | cons a actors ih =>
    cases a with
    -- The Character's place in the list is skipped.
    | none => exact ih s
    -- Creature `i` acts, then the rest of the list.
    | some i =>
      simp only [foeTurnsWith, foeTurnWith, Bind.bind]
      repeat first
        | exact Distribution.valid_pure _
        | exact hA _ _ _ _
        | exact ih _
        | apply Distribution.valid_bind
        | split
        | intro
end

/-! ## The fast round has the odds of `roundDistribution` -/

/-- `fastFoes` has the odds of the Creature turns with `fastAttack`. -/
theorem fastFoes_correct (rules : RuleSet) (s : FightState) (actors : List Actor)
    (observe : FightState → Rat) :
    (fastFoes rules s actors).expect observe =
      (foeTurnsWith (fastAttack rules) s actors).expect (fun result => observe result.1) := by
  induction actors generalizing s observe with
  -- No turn is left.
  | nil => rfl
  -- One more turn is in the list.
  | cons actor actors ih =>
    cases actor with
    -- The Character's place in the list is skipped.
    | none => simpa [fastFoes, foeTurnsWith, Distribution.expect_bind] using ih s observe
    -- Creature `i` acts, then the rest of the list.
    | some i =>
      simp only [fastFoes, Distribution.expect_sortCollect, Distribution.expect_bind,
        Distribution.expect_map, foeTurnsWith]
      change ((foeTurnWith (fastAttack rules) s i).bind _).expect _ = _
      simp only [Bind.bind, Distribution.expect_bind, Distribution.expect_pure]
      congr 1
      funext result
      exact ih result.1 observe

/-- `fastRound` has the odds of the Engine round with `fastAttack`. -/
theorem fastRound_correct (rules : RuleSet) (order : List Actor) (s : FightState)
    (observe : FightState → Rat) :
    (fastRound rules order s).expect observe =
      (roundWith (fastAttack rules) heroPolicy order s).expect (fun result => observe result.1) := by
  simp only [fastRound, Distribution.expect_sortCollect, Distribution.expect_bind]
  rw [fastFoes_correct]
  simp only [roundWith, Bind.bind, Distribution.expect_bind]
  congr 1
  funext before
  split <;> simp only [Distribution.expect_bind, Distribution.expect_pure]
  -- The Fight is over before the Character's turn.
  · exact fastFoes_correct rules before.1 (afterCharacter order) observe
  -- The Character acts, then the Creatures after it.
  · congr 1
    funext choice
    simp only [Distribution.expect_map]
    congr 1
    funext after
    exact fastFoes_correct rules after.1 (afterCharacter order) observe

/-- The main fact of this file: for every observable of the state after the round, `fastRound`
and `roundDistribution` with `heroPolicy` give the same expected value. -/
theorem fastRound_expect (rules : RuleSet) (order : List Actor) (s : FightState)
    (observe : FightState → Rat) :
    (fastRound rules order s).expect observe =
      (roundDistribution rules heroPolicy order s).expect observe := by
  rw [fastRound_correct, roundDistribution_correct]
  exact (round_forgets (fastAttack_forgets rules) heroPolicy order s observe).symm

/-- `fastFoes` is a probability distribution. -/
theorem fastFoes_valid (rules : RuleSet) (s : FightState) (actors : List Actor) :
    (fastFoes rules s actors).Valid := by
  induction actors generalizing s with
  -- No Creature acts.
  | nil => exact Distribution.valid_pure _
  -- One Creature acts, then the rest.
  | cons a actors ih =>
    apply Distribution.valid_sortCollect
    apply Distribution.valid_bind
    -- The first turn.
    · exact Distribution.valid_sortCollect _ _
        (Distribution.valid_map _ _ (foeTurnsWith_valid (fastAttack_valid rules) _ _))
    -- The other turns.
    · exact ih

/-- `fastRound` is a probability distribution. -/
theorem fastRound_valid (rules : RuleSet) (order : List Actor) (s : FightState) :
    (fastRound rules order s).Valid := by
  unfold fastRound
  apply Distribution.valid_sortCollect
  apply Distribution.valid_bind
  -- The Creatures before the Character, then the Character.
  · apply Distribution.valid_sortCollect
    apply Distribution.valid_bind _ _ (fastFoes_valid _ _ _)
    intro u
    split
    -- The Fight is over, so the Character does not act.
    · exact Distribution.valid_pure _
    -- The Character acts.
    · next hu =>
      apply Distribution.valid_bind _ _ (heroPolicy_valid u (Bool.eq_false_iff.mpr hu))
      intro choice
      exact Distribution.valid_map _ _ (heroTurnWith_valid (fastAttack_valid rules) _ _ _)
  -- The Creatures after the Character.
  · intro u
    exact fastFoes_valid _ _ _

/-- `fastStep` is a probability distribution. -/
theorem fastStep_valid (rules : RuleSet) (order : List Actor) (s : FightState) :
    (fastStep rules order s).Valid := by
  unfold fastStep
  split
  -- The Fight is over and stays as it is.
  · exact Distribution.valid_pure _
  -- One round.
  · exact fastRound_valid rules order s

/-! ## The wording and the order of the combat rules do not matter

The fast round reads a combat rule only through its side, its trigger and its three numbers, and
it adds the numbers of the rules that are active. So two lists of rules with the same effects, in
any order, give the same round. The server uses this to reuse a checked paused Fight. -/

/-- The effect of a combat rule: the rule with no name and no description. -/
def _root_.Rpg.CombatRule.effect (r : CombatRule) : CombatRule :=
  {name := "", description := "", side := r.side, trigger := r.trigger,
   hitBonus := r.hitBonus, damageBonus := r.damageBonus, armorBonus := r.armorBonus}

/-- Two lists of integers in a different order have the same sum. -/
theorem perm_sum_int {a b : List Int}
    -- `b` is `a` in another order.
    (h : a.Perm b) :
    a.sum = b.sum := by
  induction h with
  -- Two empty lists.
  | nil => rfl
  -- The same first item.
  | cons x _ ih => simp [ih]
  -- The first two items change places.
  | swap x y l => simp; omega
  -- Two steps of reordering.
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- If two lists of rules have the same effects in some order, then a filter and a map that read
only the effect give the same items in some order. -/
theorem map_filter_perm {β : Type} {A B : List CombatRule}
    -- The effects of `B` are the effects of `A` in some order.
    (h : (A.map CombatRule.effect).Perm (B.map CombatRule.effect))
    (P : CombatRule → Bool) (g : CombatRule → β)
    -- `P` reads only the effect.
    (hP : ∀ x, P x.effect = P x)
    -- `g` reads only the effect.
    (hg : ∀ x, g x.effect = g x) :
    ((A.filter P).map g).Perm ((B.filter P).map g) := by
  have onEffects (L : List CombatRule) :
      (L.filter P).map g = ((L.map CombatRule.effect).filter P).map g := by
    rw [List.filter_map, List.map_map]
    have e1 : P ∘ CombatRule.effect = P := funext hP
    have e2 : g ∘ CombatRule.effect = g := funext hg
    rw [e1, e2]
  rw [onEffects A, onEffects B]
  exact (h.filter P).map g

/-- The injury of an attack is the same with combat rules `B` as with the rules of `r`, if `B` has
the same effects in some order. -/
theorem injuryDistribution_effects (r : RuleSet) (B : List CombatRule)
    -- The effects of `B` are the effects of the rules of `r` in some order.
    (h : (r.combatRules.map CombatRule.effect).Perm (B.map CombatRule.effect))
    (a : Actor) (att : Fighter) (b : Actor) (dfn : Fighter) :
    injuryDistribution {r with combatRules := B} a att b dfn = injuryDistribution r a att b dfn := by
  have hit := perm_sum_int (map_filter_perm h
    (fun x => x.active r a att dfn && (x.hitBonus != 0 || x.damageBonus != 0)) (·.hitBonus)
    (fun _ => rfl) (fun _ => rfl))
  have dmg := perm_sum_int (map_filter_perm h
    (fun x => x.active r a att dfn && (x.hitBonus != 0 || x.damageBonus != 0)) (·.damageBonus)
    (fun _ => rfl) (fun _ => rfl))
  have arm := (map_filter_perm h
    (fun x => x.active r b dfn att && decide (x.armorBonus > 0)) (·.armorBonus)
    (fun _ => rfl) (fun _ => rfl)).sum_nat
  -- A rule reads only the HP limit of the rules, which the two rule sets share.
  have same (x : CombatRule) (i : Actor) (f g : Fighter) :
      x.active {r with combatRules := B} i f g = x.active r i f g := rfl
  simp only [injuryDistribution, same]
  rw [← hit, ← dmg, ← arm]
  rfl

/-- The fast attack is the same with combat rules `B`, if `B` has the effects of the rules of `r`
in some order. -/
theorem fastAttack_effects (r : RuleSet) (B : List CombatRule)
    -- The effects of `B` are the effects of the rules of `r` in some order.
    (h : (r.combatRules.map CombatRule.effect).Perm (B.map CombatRule.effect)) :
    fastAttack {r with combatRules := B} = fastAttack r := by
  funext a att b dfn
  simp only [fastAttack, injuryDistribution_effects r B h]

/-- The turns of the Creatures are the same with combat rules `B`, as for `fastAttack_effects`. -/
theorem fastFoes_effects (r : RuleSet) (B : List CombatRule)
    -- The effects of `B` are the effects of the rules of `r` in some order.
    (h : (r.combatRules.map CombatRule.effect).Perm (B.map CombatRule.effect)) :
    fastFoes {r with combatRules := B} = fastFoes r := by
  funext s actors
  induction actors generalizing s with
  -- No turns.
  | nil => rfl
  -- One turn, then the rest.
  | cons a rest ih => simp only [fastFoes, fastAttack_effects r B h, ih]

/-- One fast round is the same with combat rules `B`, as for `fastAttack_effects`. -/
theorem fastStep_effects (r : RuleSet) (B : List CombatRule)
    -- The effects of `B` are the effects of the rules of `r` in some order.
    (h : (r.combatRules.map CombatRule.effect).Perm (B.map CombatRule.effect))
    (order : List Actor) :
    fastStep {r with combatRules := B} order = fastStep r order := by
  funext s
  simp only [fastStep, fastRound, fastFoes_effects r B h, fastAttack_effects r B h]

end Rpg.Probability
