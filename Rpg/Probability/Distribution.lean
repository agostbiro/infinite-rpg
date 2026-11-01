import Init.Data.Rat

/-! Exact finite distributions. Duplicate entries represent distinct dice paths;
`collect` combines paths that reach the same result. -/
namespace Rpg.Probability

/-- A finite list of values with exact rational weights. -/
structure Distribution (α : Type) where
  entries : List (α × Rat)
  deriving Repr, DecidableEq

/-- Combine two independent stages, multiplying their path weights. -/
def Distribution.bind (d : Distribution α) (f : α → Distribution β) : Distribution β :=
  ⟨d.entries.flatMap fun (x, p) => (f x).entries.map fun (y, q) => (y, p * q)⟩

instance : Monad Distribution where
  pure x := ⟨[(x, 1)]⟩
  bind := Distribution.bind

/-- Sum the weights of results satisfying a test. -/
def Distribution.mass (d : Distribution α) (test : α → Bool) : Rat :=
  (d.entries.map fun (x, p) => if test x then p else 0).sum

/-- A probability distribution has nonnegative weights with total one. -/
def Distribution.Valid (d : Distribution α) : Prop :=
  (∀ e ∈ d.entries, 0 ≤ e.2) ∧ (d.entries.map Prod.snd).sum = 1

/-- Merge equal results and remove zero-weight entries. -/
def Distribution.collect [DecidableEq α] (d : Distribution α) : Distribution α :=
  ⟨d.entries.foldl (fun acc (x, p) =>
    if p = 0 then acc
    else if acc.any (fun e => decide (e.1 = x)) then
      acc.map fun (y, q) => (y, if x = y then p + q else q)
    else (x, p) :: acc) []⟩

/-- Choose each list position with equal probability. Empty input has no mass. -/
def uniform (xs : List α) : Distribution α :=
  ⟨xs.map fun x => (x, 1 / (xs.length : Rat))⟩

/-- The exact sum distribution of independent fair six-sided dice. -/
def dice : Nat → Distribution Nat
  | 0 => pure 0
  | n + 1 => (do
      let a ← uniform [1, 2, 3, 4, 5, 6]
      let b ← dice n
      pure (a + b)).collect

/-- 3d6 has 216 equally likely elementary results. -/
theorem three_sixes : (dice 3).mass (· == 18) = 1 / 216 := by decide +kernel

/-- Combining duplicate paths preserves their total probability in this example. -/
example : ((uniform [1, 1, 2]).collect).mass (· == 1) = 2 / 3 := by decide +kernel

end Rpg.Probability
