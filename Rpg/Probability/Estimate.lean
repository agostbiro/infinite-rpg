import Rpg.Probability.Fairness

/-!
Bounded simulation diagnostics, NOT a fairness proof or certificate.
These use the adventure's actual engine rules. Censored runs remain unknown;
zero observed events are never treated as proof of impossibility.
Nominal simultaneous Hoeffding intervals assume independent random trajectories.
The RNG, that sampling assumption, and the concentration bound are not proved here.
The diagnostic intervals do not supply the finite `fair` theorem or admission evidence.
-/
namespace Rpg.Probability.Estimate

/-- Fixed audit settings; choose them before examining results. -/
structure Config where
  samples : Nat := 100000
  horizon : Nat := 6
  roundLimit : Nat := 200
  seed : Nat := 20261101
  failureProbability : Float := 0.001
  deriving Repr

/-- A timeout records the first turn whose outcome is unknown. -/
inductive Finish where
  | dead | ended | censored | invalid
  deriving Repr, BEq

/-- A completed outcome, or the first unresolved turn. -/
structure Trace where
  finish : Finish
  turn : Nat
  deriving Repr, BEq

/-- Choose uniformly under the ideal uniform-word assumption, up to modulo bias.
As with the engine's d6, the finite PRNG is not proved IID. -/
def choose (n : Nat) : Roll Nat := do
  if n ≤ 1 then return 0
  let (word, next) := (← get).next
  set next
  return word.toNat % n

/-- Bounded combat uses the same rounds as play; timeout is not a loss or win. -/
def fight (rules : RuleSet) (order : List Actor) : Nat → FightState → Roll (Option FightState)
  | fuel, state => do
    if state.over then return some state
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      let living := (state.foes.zipIdx.filter fun (f, _) => f.alive).map Prod.snd
      let target := living.getD (← choose living.length) 0
      let (next, _) ← fightRound rules order state target
      fight rules order fuel next

/-- One trajectory; scene choices, not combat rounds, advance its turn count. -/
def trajectory (a : AdventureDefinition) (roundLimit : Nat) :
    Nat → SceneId → Int → Nat → Roll Trace
  | fuel, id, hp, turns => do
    if hp ≤ 0 then return ⟨.dead, turns⟩
    let some scene := a.story.scene? id | return ⟨.invalid, turns⟩
    if scene.choices.isEmpty then return ⟨.ended, turns⟩
    match fuel with
    | 0 => return ⟨.censored, turns + 1⟩
    | fuel + 1 =>
      let some choice := scene.choices[← choose scene.choices.length]?
        | return ⟨.invalid, turns⟩
      match choice.outcome with
      | .goto next => trajectory a roundLimit fuel next hp (turns + 1)
      | .roll target modifier yes no =>
        let level := (a.hero.rollLevel a.rules target).map (· + modifier)
        let (result, _) ← makeRoll a.rules "audit" level
        trajectory a roundLimit fuel (if result.succeeded then yes else no) hp (turns + 1)
      | .fight foes next =>
        let state : FightState := ⟨⟨a.hero, hp⟩, foes.map fun foe => ⟨foe, a.rules.maxHP foe⟩⟩
        let result ← fight a.rules (turnOrder a.rules a.hero foes) roundLimit state
        match result with
        | none => return ⟨.censored, turns + 1⟩
        | some state =>
          if !state.hero.alive then return ⟨.dead, turns + 1⟩
          trajectory a roundLimit fuel next state.hero.hp (turns + 1)

/-- Histograms retain censored runs rather than silently discarding them. -/
structure Counts where
  deaths : Array Nat
  endings : Array Nat
  censored : Array Nat
  invalid : Nat := 0
  deriving Repr

/-- Increment a histogram entry; arrays include the overflow censor bucket. -/
def bump (xs : Array Nat) (i : Nat) : Array Nat := xs.modify i (· + 1)

/-- Add one trace to the audit histograms. -/
def Counts.record (c : Counts) (trace : Trace) : Counts :=
  match trace.finish with
  | .dead => { c with deaths := bump c.deaths trace.turn }
  | .ended => { c with endings := bump c.endings trace.turn }
  | .censored => { c with censored := bump c.censored trace.turn }
  | .invalid => { c with invalid := c.invalid + 1 }

/-- Run a fixed-size batch, without optional stopping or searching for a favorable seed. -/
def sample (cfg : Config) (a : AdventureDefinition) : Counts := Id.run do
  let cap := cfg.horizon + 2
  let mut counts : Counts := ⟨Array.replicate (cap + 2) 0,
    Array.replicate (cap + 2) 0, Array.replicate (cap + 2) 0, 0⟩
  let mut rng : Rng := ⟨cfg.seed.toUInt64⟩
  for _ in [:cfg.samples] do
    let (trace, next) := (trajectory a cfg.roundLimit cap a.story.start
      (a.rules.maxHP a.hero) 0).run rng
    rng := next
    counts := counts.record trace
  return counts

/-- Histogram sum for times satisfying a predicate. -/
def total (xs : Array Nat) (p : Nat → Bool := fun _ => true) : Nat :=
  (xs.toList.zipIdx.map fun (count, t) => if p t then count else 0).sum

/-- Numeric diagnostic interval; endpoints are NOT Lean-certified enclosures. -/
structure Interval where
  lower : Float
  upper : Float
  deriving Repr

/-- Diagnostic classification; none of these constructors is a proof of fairness. -/
inductive Verdict where
  | within | violation | inconclusive
  deriving Repr, BEq

/-- Compare a whole interval with the policy band; overlap alone does not pass. -/
def classify (band : Interval) (observed : Interval) : Verdict :=
  if observed.upper < band.lower || observed.lower > band.upper then .violation
  else if band.lower ≤ observed.lower && observed.upper ≤ band.upper then .within
  else .inconclusive

/-- Nominal Hoeffding radius after a union bound over 4*horizon+10 quantities.
There are four indicator bounds per conditional row, plus first-turn and lifetime bounds. -/
def radius (cfg : Config) : Float :=
  Float.sqrt (Float.log ((2 * (4 * cfg.horizon + 10)).toFloat / cfg.failureProbability) /
    (2 * cfg.samples.toFloat))

/-- Enclose the mean of bounded observations with unknown outcomes kept as a range. -/
def meanInterval (cfg : Config) (lowerSum upperSum : Nat) : Interval :=
  ⟨max 0 (lowerSum.toFloat / cfg.samples.toFloat - radius cfg),
   min 1 (upperSum.toFloat / cfg.samples.toFloat + radius cfg)⟩

/-- A conservative ratio; a possibly zero conditioning probability is inconclusive. -/
def conditionalInterval (numerator denominator : Interval) : Interval :=
  if denominator.lower ≤ 0 then ⟨0, 1⟩
  else ⟨max 0 (numerator.lower / denominator.upper), min 1 (numerator.upper / denominator.lower)⟩

/-- First-turn death bounds include any fight censored on that turn. -/
def firstDeath (cfg : Config) (c : Counts) : Interval :=
  let deaths := c.deaths[1]!
  meanInterval cfg deaths (deaths + total c.censored (· ≤ 1) + c.invalid)

/-- Bound death at exactly t+2 conditional on being active at t. -/
def atTwo (cfg : Config) (c : Counts) (t : Nat) : Interval :=
  let activeKnown := total c.deaths (· > t) + total c.endings (· > t) + total c.censored (· > t)
  let activePossible := activeKnown + total c.censored (· ≤ t) + c.invalid
  let deaths := c.deaths[t + 2]!
  let deathPossible := deaths + total c.censored (· ≤ t + 2) + c.invalid
  conditionalInterval (meanInterval cfg deaths deathPossible)
    (meanInterval cfg activeKnown activePossible)

/-- Convert a rational for display/comparison only, avoiding huge intermediate Float casts. -/
def approximate (p : Rat) : Float :=
  (p.num * 1000000000 / p.den).toFloat / 1000000000

/-- The target band uses the exact policy function, rounded only for diagnostics. -/
def band (target tolerance : Rat) : Interval :=
  ⟨max 0 (approximate (target - tolerance)), min 1 (approximate (target + tolerance))⟩

/-- A normalized bounded-time mean, retaining lower/upper contributions from censored runs. -/
def timeInterval (cfg : Config) (lowerSum upperSum : Nat) : Interval :=
  let cap := (cfg.horizon + 2).toFloat
  let denom := cfg.samples.toFloat * cap
  ⟨max 0 (lowerSum.toFloat / denom - radius cfg) * cap,
   min 1 (upperSum.toFloat / denom + radius cfg) * cap⟩

/-- Sum observed times, capped at the audit's finite observation limit. -/
def timeSum (xs : Array Nat) (cap : Nat) : Nat :=
  (xs.toList.zipIdx.map fun (count, t) => count * min t cap).sum

/-- Bounds on E[min(termination time, cap)], not on an unbounded expectation. -/
def terminationTime (cfg : Config) (c : Counts) : Interval :=
  let cap := cfg.horizon + 2
  let known := timeSum c.deaths cap + timeSum c.endings cap
  timeInterval cfg (known + timeSum c.censored cap)
    (known + (total c.censored + c.invalid) * cap)

/-- Successful endings have infinite death time, so contribute the full cap here. -/
def deathTime (cfg : Config) (c : Counts) : Interval :=
  let cap := cfg.horizon + 2
  let known := timeSum c.deaths cap + total c.endings * cap
  timeInterval cfg (known + timeSum c.censored cap)
    (known + (total c.censored + c.invalid) * cap)

/-- Bounds on E[T | death by cap]; undefined conditioning is reported as no estimate. -/
def conditionalDeathTime (cfg : Config) (c : Counts) : Option Interval :=
  let cap := cfg.horizon + 2
  let probability := meanInterval cfg (total c.deaths)
    (total c.deaths + total c.censored (· ≤ cap) + c.invalid)
  if probability.lower ≤ 0 then none
  else
    let moment := timeInterval cfg (timeSum c.deaths cap)
      (timeSum c.deaths cap + (total c.censored (· ≤ cap) + c.invalid) * cap)
    some ⟨max 0 (moment.lower / probability.upper), min cap.toFloat (moment.upper / probability.lower)⟩

end Rpg.Probability.Estimate
