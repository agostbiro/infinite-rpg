import Rpg.Live

/-! Tune encounter parameters on a screening batch before the independent validity test.
The search never changes the fairness policy, graph edges, hero or validation seed. -/
namespace Rpg
open Probability

/-- A fixed training seed, separate from the seed chosen after the draft is frozen. -/
def balanceSeed : Nat := 20261101

/-- Adjust enemy strength and learned combat skill, keeping their names and equipment. -/
def tuneFoe (b : Being) (strength skill : Int) : Being :=
  { b with st := (max (Int.ofNat b.weapon.minST) (min 20 (Int.ofNat b.st + strength))).toNat
           skills := b.skills.map fun (s,l) =>
             (s, if s == b.weapon.skill then (max 1 (Int.ofNat l + skill)).toNat else l) }

/-- Tuning changes only foes, so all scene choices retain their original destinations. -/
def Draft.tune (d : Draft) (strength skill : Int) : Draft :=
  { d with adventure := { d.adventure with scenes := d.adventure.scenes.map fun s =>
      { s with choices := s.choices.map fun c => { c with outcome := match c.outcome with
        | .fight foes next => .fight (foes.map (tuneFoe · strength skill)) next
        | other => other } } } }

/-- Prefer observations near the policy centre, with a large penalty for sparse rows.
The ten-turn survival target guides tuning; admission still uses the original interval test. -/
def balanceScore (a : StatisticalCandidate) (c : ValidationCounts) : Rat :=
  if c.aborted then 100000 else Id.run do
    let mut score : Rat := 0
    for row in [:a.horizon+1] do
      let n := c.trials[row]!
      let p : Rat := (c.deaths[row]! : Rat) / max 1 n
      let target := if row == 0 then 1 - a.policy.survival 1 else a.policy.deathAtTwo (row-1)
      let difference := p-target
      score := score + difference*difference + (if n < 20 then 10 else 0)
    let deaths : Nat := (List.range 10).foldl (fun n i => n + c.deaths[i]!) 0
    let difference := 1 - (deaths : Rat)/max 1 c.games - a.policy.survival 10
    return score + 4*difference*difference

/-- Try a bounded parameter grid on training data only. Progress also permits cancellation. -/
def balanceDraft (draft : Draft) (progress : Nat → IO Bool) : IO (Except (List String) Draft) := do
  match draft.checked with
  | .error errors => return .error errors
  | .ok _ => pure ()
  let mut best := draft
  let mut bestScore : Rat := 1000000
  let mut bestStrength : Int := 0
  let mut bestSkill : Int := 0
  let mut index := 0
  for strength in ([0, -2, 2, -4, 4] : List Int) do
    for skill in ([0, -2, 2] : List Int) do
      index := index + 1
      if !(← progress index) then return .error ["Balancing cancelled"]
      let candidate := draft.tune strength skill
      match candidate.checked with
      | .error _ => pure ()
      | .ok checked =>
        let a := liveCandidate checked candidate.validationProfile
        let counts := sampleCounts a balanceSeed 256
        let score := balanceScore a counts
        if score < bestScore then
          best := candidate
          bestScore := score
          bestStrength := strength
          bestSkill := skill
  let .ok checked := best.checked | return .error best.errors
  let candidate := liveCandidate checked best.validationProfile
  let (counts, accepted) := admitWithSeed candidate balanceSeed
  if accepted.isSome then return .ok best
  return .error ([s!"Training measurements use enemy ST offset {bestStrength} and weapon skill offset {bestSkill} from your draft."] ++ (failedRows candidate.horizon counts candidate.policy).map
    ("balance training: " ++ ·) ++
    ["Local encounter tuning did not suffice. Change fight frequency, safe branches and their depth in the event graph; keep the selected fairness policy unchanged."])

end Rpg
