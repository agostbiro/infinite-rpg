import Rpg.Adventures.Lighthouse.Definition
import Rpg.Probability.Estimate

open Rpg Rpg.Probability Rpg.Probability.Estimate

/-- Read numeric audit options, rejecting missing or malformed values. -/
def parseConfig : List String → Config → Except String Config
  | [], cfg => .ok cfg
  | key :: value :: rest, cfg => do
    let some n := value.toNat? | throw s!"Invalid number for {key}: {value}"
    let cfg ← match key with
      | "--samples" => pure { cfg with samples := n }
      | "--horizon" => pure { cfg with horizon := n }
      | "--round-limit" => pure { cfg with roundLimit := n }
      | "--seed" => pure { cfg with seed := n }
      | _ => throw s!"Unknown audit option: {key}"
    parseConfig rest cfg
  | [_], _ => .error "Audit options require a numeric value."

/-- Print a diagnostic interval without implying a formal certificate. -/
def showInterval (x : Interval) : String := s!"[{x.lower}, {x.upper}]"

/-- Human-readable diagnostic status. -/
def statusName : Verdict → String
  | .within => "WITHIN (diagnostic only)"
  | .violation => "VIOLATION (diagnostic only)"
  | .inconclusive => "INCONCLUSIVE"

/-- Audit Lighthouse using the current source and rules; never alter the playable catalog. -/
def main (args : List String) : IO UInt32 := do
  let .ok cfg := parseConfig args {} | do
    IO.eprintln "Usage: lake exe audit [--samples N] [--horizon H] [--round-limit R] [--seed S]"
    return 2
  if cfg.samples = 0 || cfg.horizon = 0 || cfg.horizon > 128 || cfg.roundLimit = 0 then
    IO.eprintln "Samples and round limit must be positive; horizon must be between 1 and 128."
    return 2
  IO.println "LIGHTHOUSE PROBABILITY AUDIT — DIAGNOSTICS ONLY, NOT A LEAN FAIRNESS PROOF"
  IO.println s!"samples={cfg.samples} seed={cfg.seed} horizon={cfg.horizon} combat-round-limit={cfg.roundLimit}"
  IO.println "Nominal simultaneous confidence: 99.9%, conditional on IID sampling assumptions."
  IO.println "The PRNG assumptions, Hoeffding bound, and floating-point endpoints are not proved in Lean."
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let counts := sample cfg Lighthouse.lighthouseDefinition
  IO.println s!"elapsed-ms={((← IO.monoMsNow) - start)}"
  IO.println s!"deaths={total counts.deaths} endings={total counts.endings} censored={total counts.censored} invalid={counts.invalid}"
  IO.println s!"death histogram: {counts.deaths.toList}"
  IO.println s!"ending histogram: {counts.endings.toList}"
  IO.println s!"censor histogram: {counts.censored.toList}"
  let firstBand := band (1 - defaultPolicy.survival 1) defaultPolicy.tolerance
  let first := firstDeath cfg counts
  let mut violation := classify firstBand first == .violation
  let mut uncertain := classify firstBand first == .inconclusive
  IO.println s!"first turn: {showInterval first}, allowed {showInterval firstBand}: {statusName (classify firstBand first)}"
  for t in [:cfg.horizon] do
    let interval := atTwo cfg counts t
    let allowed := band (defaultPolicy.deathAtTwo t) defaultPolicy.tolerance
    let verdict := classify allowed interval
    violation := violation || verdict == .violation
    uncertain := uncertain || verdict == .inconclusive
    IO.println s!"t={t}, death at {t+2} | active at {t}: {showInterval interval}, allowed {showInterval allowed}: {statusName verdict}"
  let cap := cfg.horizon + 2
  IO.println s!"E[min(termination time, {cap})]: {showInterval (terminationTime cfg counts)}"
  IO.println s!"E[min(death time, {cap})]: {showInterval (deathTime cfg counts)}"
  match conditionalDeathTime cfg counts with
  | none => IO.println "E[death time | death by cap]: INCONCLUSIVE (conditioning probability may be zero)"
  | some interval => IO.println s!"E[death time | death by {cap}]: {showInterval interval}"
  if counts.invalid > 0 then
    IO.println "RESULT: invalid simulation states; audit is not usable."
    return 2
  if violation then
    IO.println "RESULT: estimated policy violation. No fairness certificate was produced."
    return 1
  if uncertain then
    IO.println "RESULT: inconclusive. No fairness certificate was produced."
    return 0
  IO.println "RESULT: finite-window diagnostic bounds fit. Run make validate for the proved confidence protocol."
  IO.println "Exploratory intervals do not supply admission evidence."
  return 0
