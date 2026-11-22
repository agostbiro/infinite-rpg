import MarkovRPGCombatState
import MarkovRPGDistributions
import Mathlib.Probability.Distributions.Uniform

/-!
# The generic alternating combat graph

The inputs are two globally admissible characters under one fixed rulebook.
Actions are Attack, Defend, and the available inventory bonuses; there is no
All-Out Attack. Both players use the same action semantics. A policy turns the
controlled graph into a Markov chain; uniform choice is supplied for tests.

All existing ItemEffect constructors are interpreted. Passive bonuses are
evaluated once, timed bonuses refresh their own source slot, and consumables
spend one unit. Effect order is the item's list order. Effective scores are
clamped to the global limits. Action statistics are read at action start; old
timers tick once and newly installed timers retain their full duration.

Attack uses main's 3d6 success rules, Dodge, damage types and weapon tables.
Critical success bypasses Dodge, and an attack total of 3 maximizes damage dice.
This imports the shared core mechanics, not adventure-specific world rules.

Win/Lose are absorbing OUTPUT LABELS of bounded vertices. Final HP, stocks,
and effect timers are retained. Finiteness alone is not a termination proof:
two participants can choose Defend forever, or be unable to hurt one another.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal ENNReal

namespace MarkovRPG.Combat
set_option backward.isDefEq.respectTransparency false
open MainRules

variable {r : Rules}

def Setup.passiveModifiers (c : Setup r) (s : Vertex r) (p : Player) : List Modifier :=
  (List.finRange r.itemSlots).flatMap fun i =>
    if c.equipped p i && (s.stock p i).val > 0 then
      ((c.item? p i).map (fun item => item.effects.filterMap fun e => match e with
        | .whileEquipped m => some m
        | _ => none)).getD []
    else []

def Setup.modifierSum (c : Setup r) (s : Vertex r) (p : Player)
    (property : CharacterProperty) : Int :=
  ((c.passiveModifiers s p).map fun m => if m.property = property then Modifier.amount m else 0).sum +
    ∑ key : EffectKey r, if (s.remaining p key).val > 0 then
      match c.modifier? key with
      | some m => if m.property = property then Modifier.amount m else 0
      | none => 0
    else 0

def boundedScore (bound : Nat) (score : Int) : Nat := min score.toNat bound

def Setup.effectiveBeing (c : Setup r) (s : Vertex r) (p : Player) : Being :=
  let raw := (c.characters p).character
  let base := raw.toBeing ""
  let attributeScore := fun a => boundedScore r.attributeMax
    ((base.attr a : Int) + c.modifierSum s p (.attribute a))
  let updated : Being := { base with
    st := attributeScore .st
    dx := attributeScore .dx
    iq := attributeScore .iq
    ht := attributeScore .ht
    armor := .none
    naturalDR := (boundedScore r.protectionMax
      ((raw.statistics.naturalDR : Int) + c.modifierSum s p .protection)) }
  { updated with skills := Skill.all.filterMap fun skill =>
      (updated.skillLevel skill).map fun score =>
        (skill, boundedScore r.skillMax (score + c.modifierSum s p (.skill skill))) }

/-- Resource modifiers are evaluated with the same lifetime semantics as all
other modifiers. Resource IDs belong to the static character/item data. -/
def Setup.effectiveResource (c : Setup r) (s : Vertex r) (p : Player)
    (id : ResourceId) : Nat :=
  let base := (((c.characters p).character.resources.find? (fun x => x.1 == id)).map
    Prod.snd).getD 0
  boundedScore r.resourceMax ((base : Int) + c.modifierSum s p (.resource id))

def Setup.dodge (c : Setup r) (s : Vertex r) : Nat :=
  let defender := s.turn.other
  let base := (c.effectiveBeing s defender).dodge
  let wounded := if r.halveDodgeBelowThird && 3 * (s.hp defender).val < r.hpMax
    then (base + 1) / 2 else base
  wounded + if s.guarded then r.defenseBonus else 0

/-- Each face is independent and uniform on 1,...,6. This representation avoids
enumerating the full combat graph to describe one transition. -/
def diceSum (count : Nat) : PMF Nat :=
  (PMF.uniformOfFintype (Fin count → Fin 6)).map (fun faces => ∑ i, ((faces i).val + 1))

def Setup.damageLaw (c : Setup r) (snapshot : Vertex r) (actor target : Player)
    (spec : DamageSpec) (maximized : Bool) : PMF Nat :=
  let strength := (c.effectiveBeing snapshot actor).st
  let protection := (c.effectiveBeing snapshot target).dr
  let evaluate := fun total => min (spec.injury strength total protection) r.damageMax
  match spec with
  | .fixed _ _ => PMF.pure (evaluate 0)
  | .roll dice _ =>
    if maximized then PMF.pure (evaluate (6 * dice.count))
    else (diceSum dice.count).map evaluate
  | .weapon w =>
    if maximized then PMF.pure (evaluate (6 * (w.damage strength).count))
    else (diceSum (w.damage strength).count).map evaluate

/-- For a duel, allOpponents and opponent select the same participant. -/
def recipient (actor : Player) : EffectTarget → Player
  | .self => actor
  | .opponent | .allOpponents => actor.other

def Vertex.tick (s : Vertex r) : Vertex r :=
  { s with remaining := fun p key => clamp r.durationMax ((s.remaining p key).val - 1) }

def Vertex.install (s : Vertex r) (target : Player) (key : EffectKey r)
    (duration : Nat) : Vertex r :=
  { s with remaining := (Function.update s.remaining target
      (Function.update (s.remaining target) key (clamp r.durationMax duration))) }

def Setup.spendBonus (c : Setup r) (s : Vertex r) (i : Fin r.itemSlots) : Vertex r :=
  match c.item? s.turn i with
  | some item => if item.usage = .consumable then
      { s with stock := (Function.update s.stock s.turn
          (Function.update (s.stock s.turn) i (clamp r.stockMax ((s.stock s.turn i).val - 1)))) }
    else s
  | none => s

inductive Trigger where
  | use
  | hit
  deriving DecidableEq

def Setup.applyEffect (c : Setup r) (snapshot : Vertex r) (actor : Player)
    (trigger : Trigger) (maximized : Bool) (key : EffectKey r) (effect : ItemEffect)
    (s : Vertex r) : PMF (Vertex r) :=
  match trigger, effect with
  | .use, .onUse target (.heal amount) => PMF.pure (s.heal (recipient actor target) amount)
  | .use, .onUse target (.damage spec)
  | .hit, .onHit target spec =>
    (c.damageLaw snapshot actor (recipient actor target) spec maximized).map
      (fun amount => s.hurt (recipient actor target) amount)
  | .use, .timedOnUse target _ duration =>
    PMF.pure (s.install (recipient actor target) key duration.val)
  | _, _ => PMF.pure s

/-- Resolution stops as soon as an output is reached, so subsequent item
effects cannot resurrect a defeated participant within the same action. -/
def Setup.applyEffects (c : Setup r) (snapshot : Vertex r) (actor : Player)
    (trigger : Trigger) (maximized : Bool) :
    List (EffectKey r × ItemEffect) → Vertex r → PMF (Vertex r)
  | [], s => PMF.pure s
  | (key, effect) :: rest, s =>
    if s.output.isSome then PMF.pure s
    else (c.applyEffect snapshot actor trigger maximized key effect s).bind
      (fun next => c.applyEffects snapshot actor trigger maximized rest next)

def Setup.itemEffects (c : Setup r) (p : Player) (i : Fin r.itemSlots) :
    List (EffectKey r × ItemEffect) :=
  (List.finRange r.effectsPerSource).filterMap fun e =>
    (c.effect? p i e).map (fun effect => (.item p i e, effect))

/-- Bare-handed damage has no inventory source and is handled separately. -/
def Setup.hitEffects (c : Setup r) (s : Vertex r) : List (EffectKey r × ItemEffect) :=
  (List.finRange r.itemSlots).flatMap fun i =>
    if c.equipped s.turn i && (s.stock s.turn i).val > 0 then c.itemEffects s.turn i else []

def Setup.onHit (c : Setup r) (snapshot working : Vertex r) (maximized : Bool) :
    PMF (Vertex r) :=
  let applyItems := c.applyEffects snapshot snapshot.turn .hit maximized (c.hitEffects snapshot)
  if (c.characters snapshot.turn).character.equipment.weapon.isNone then
    (c.damageLaw snapshot snapshot.turn snapshot.turn.other (.weapon .punch) maximized).bind
      (fun amount => applyItems (working.hurt snapshot.turn.other amount))
  else applyItems working

def Setup.attack (c : Setup r) (snapshot working : Vertex r) : PMF (Vertex r) :=
  let level := (c.effectiveBeing snapshot snapshot.turn).attackLevel
  if level < r.minimumRollLevel then PMF.pure working
  else (diceSum 3).bind fun attackRoll =>
    let result := MainRules.successRoll level attackRoll
    if !result.succeeded then PMF.pure working
    else if result = .criticalSuccess then c.onHit snapshot working (attackRoll = 3)
    else (diceSum 3).bind fun defenseRoll =>
      if (MainRules.successRoll (c.dodge snapshot) defenseRoll).succeeded then PMF.pure working
      else c.onHit snapshot working false

def Setup.actionBody (c : Setup r) (s : Vertex r) : Action r → PMF (Vertex r)
  | .attack => c.attack s s.tick
  | .defend => PMF.pure s.tick
  | .bonus i => c.applyEffects s s.turn .use false (c.itemEffects s.turn i)
      (c.spendBonus s.tick i)

def finishTurn (s next : Vertex r) (action : Action r) : Vertex r :=
  { next with turn := s.turn.other, guarded := action == .defend }

/-- The transition law conditional on an action. Terminal vertices are absorbing.
Unavailable actions are totalized to a self-loop; policies below cannot pick them. -/
def Setup.kernel (c : Setup r) (s : Vertex r) (action : Action r) : PMF (Vertex r) :=
  if s.output.isSome then PMF.pure s
  else if c.enabled s action then (c.actionBody s action).map (fun next => finishTurn s next action)
  else PMF.pure s

theorem Setup.kernel_absorbing (c : Setup r) (s : Vertex r) (o : Outcome)
    (ho : s.output = some o) (action : Action r) : c.kernel s action = PMF.pure s := by
  simp [kernel, ho]

theorem Setup.defend_kernel (c : Setup r) (s : Vertex r) (hs : s.output = none) :
    c.kernel s .defend = PMF.pure (finishTurn s s.tick .defend) := by
  simp [kernel, hs, enabled, actionBody, PMF.pure_map]

theorem Setup.kernel_alternates (c : Setup r) (s next : Vertex r) (a : Action r)
    (hs : s.output = none) (ha : c.enabled s a = true)
    (hn : next ∈ (c.kernel s a).support) : next.turn = s.turn.other := by
  have hk : c.kernel s a = (c.actionBody s a).map (fun v => finishTurn s v a) := by
    simp [kernel, hs, ha]
  rw [hk, PMF.mem_support_map_iff] at hn
  obtain ⟨v, _, rfl⟩ := hn
  rfl

/-- Defending changes no HP, gives the opponent the next turn, and protects the
defender during that next turn. It never suppresses the opponent's attack. -/
theorem defend_spec (s : Vertex r) :
    (finishTurn s s.tick .defend).hp = s.hp ∧
    (finishTurn s s.tick .defend).turn = s.turn.other ∧
    (finishTurn s s.tick .defend).guarded = true := by simp [finishTurn, Vertex.tick]

/-- Only admissible choices can receive policy mass. A separate decision law can
be used for each player by inspecting `s.turn`. -/
structure Policy (c : Setup r) where
  choose : (s : Vertex r) → PMF {a : Action r // c.enabled s a = true}

def uniformPolicy (c : Setup r) : Policy c where
  choose s := by
    letI : Nonempty {a : Action r // c.enabled s a = true} := ⟨⟨.attack, rfl⟩⟩
    exact PMF.uniformOfFintype _

def Setup.row (c : Setup r) (policy : Policy c) (s : Vertex r) : PMF (Vertex r) :=
  (policy.choose s).bind (fun a => c.kernel s a.val)

theorem Setup.row_absorbing (c : Setup r) (policy : Policy c) (s : Vertex r)
    (o : Outcome) (ho : s.output = some o) : c.row policy s = PMF.pure s := by
  simp [row, c.kernel_absorbing s o ho, PMF.bind_const]

/-- PMF normalization gives a stochastic matrix; it is proved, not assumed. -/
theorem pmf_sum_toReal {S : Type*} [Fintype S] (p : PMF S) :
    ∑ x, (p x).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)]
  have h : ∑ x, p x = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h]
  rfl

/-- `goal = none` measures termination in either output; `some o` measures o. -/
def Setup.chain (c : Setup r) (policy : Policy c) (goal : Option Outcome) :
    MarkovChain (Vertex r) Outcome where
  initial := c.initial
  label := Vertex.output
  transition s next := (c.row policy s next).toReal
  transition_nonneg _ _ := ENNReal.toReal_nonneg
  transition_sum s := pmf_sum_toReal (c.row policy s)
  defeat := {s | match goal with
    | none => s.output.isSome = true
    | some o => s.output = some o}

theorem Setup.edge_alternates (c : Setup r) (policy : Policy c) (goal : Option Outcome)
    (s next : Vertex r) (hs : s.output = none)
    (edge : (c.chain policy goal).Edge s next) : next.turn = s.turn.other := by
  change 0 < (c.row policy s next).toReal at edge
  have hn : next ∈ (c.row policy s).support := by
    change c.row policy s next ≠ 0
    intro hz
    simp [hz] at edge
  rw [row, PMF.mem_support_bind_iff] at hn
  obtain ⟨a, _, hn⟩ := hn
  exact c.kernel_alternates s next a.val hs a.property hn

def winProbability (c : Setup r) (policy : Policy c) (s : Vertex r) : ℝ :=
  (c.chain policy (some .Win)).hInf s

def loseProbability (c : Setup r) (policy : Policy c) (s : Vertex r) : ℝ :=
  (c.chain policy (some .Lose)).hInf s

def terminationProbability (c : Setup r) (policy : Policy c) (s : Vertex r) : ℝ :=
  (c.chain policy none).hInf s

/-- Almost-sure termination is a property to prove for the chosen combat AND
policy. It does not follow merely from the finite type of vertices. -/
def IsTerminating (c : Setup r) (policy : Policy c) (s : Vertex r) : Prop :=
  terminationProbability c policy s = 1

/-- Reuse the existing fairness interval; no two-event stability is imposed on
the internal combat graph. Parameter order remains upper p, lower q. -/
def IsFair (c : Setup r) (policy : Policy c) (s : Vertex r) (p q : ℝ) : Prop :=
  (c.chain policy (some .Lose)).IsMarkovpqFair s p q

/-- A proper duration distribution is compared to Win OR Lose, not to loss alone. -/
def HasDurationDistribution (c : Setup r) (policy : Policy c) (s : Vertex r)
    (D : MeasureTheory.ProbabilityMeasure (WithTop Nat)) (ε : ℝ≥0) : Prop :=
  (c.chain policy none).IsMarkovFairDistrib s D ε

/-- Loss-time subdistributions can independently include mass at infinity. -/
def HasLossDistribution (c : Setup r) (policy : Policy c) (s : Vertex r)
    (D : MeasureTheory.ProbabilityMeasure (WithTop Nat)) (ε : ℝ≥0) : Prop :=
  (c.chain policy (some .Lose)).IsMarkovFairDistrib s D ε

end MarkovRPG.Combat
