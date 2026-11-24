/-!
# Work on many cores

`parallelMap` and `parallelAll` split a list into pieces and run each piece as a `Task`.
In the logic, `(Task.spawn f).get` is `f ()`, so they mean the same as `List.map` and
`List.all`. `parallelAll_sound` proves this for `parallelAll`, which the combat checker uses.
-/
namespace Rpg.Probability

/-- Split `xs` into pieces of `n` items, with fewer items in the last piece. -/
def chunksOf (n : Nat) (xs : List α) : List (List α) :=
  go xs.length xs
where
  /-- Split with `fuel` steps at most. -/
  go : Nat → List α → List (List α)
    | 0, xs => [xs]
    | _ + 1, [] => []
    | fuel + 1, x :: rest => (x :: rest).take n :: go fuel ((x :: rest).drop n)

/-- The pieces, put back together, are the list. -/
theorem chunksOf_flatten (n : Nat) (xs : List α) : (chunksOf n xs).flatten = xs := by
  have go : ∀ fuel (ys : List α), (chunksOf.go n fuel ys).flatten = ys := by
    intro fuel
    induction fuel with
    | zero => intro ys; simp [chunksOf.go]
    | succ fuel ih =>
      intro ys
      cases ys with
      | nil => simp [chunksOf.go]
      | cons y rest => simp only [chunksOf.go, List.flatten_cons, ih, List.take_append_drop]
  exact go _ xs

/-- The size of a piece, so that `xs` splits into about `pieces` pieces. -/
def pieceSize (pieces : Nat) (xs : List α) : Nat :=
  max 1 ((xs.length + pieces - 1) / pieces)

/-- `List.map`, with the pieces of the list on different cores. -/
def parallelMap (f : α → β) (xs : List α) (pieces : Nat := 64) : List β :=
  let tasks := (chunksOf (pieceSize pieces xs) xs).map fun part => Task.spawn fun _ => part.map f
  tasks.flatMap Task.get

/-- `List.all`, with the pieces of the list on different cores. -/
def parallelAll (p : α → Bool) (xs : List α) (pieces : Nat := 64) : Bool :=
  let tasks := (chunksOf (pieceSize pieces xs) xs).map fun part => Task.spawn fun _ => part.all p
  tasks.all Task.get

/-- If `parallelAll p xs` is true, then `p` is true on each item of `xs`. -/
theorem parallelAll_sound {p : α → Bool} {xs : List α} {pieces : Nat}
    (h : parallelAll p xs pieces = true) : ∀ x ∈ xs, p x = true := by
  intro x hx
  simp only [parallelAll, List.all_map, List.all_eq_true] at h
  rw [← chunksOf_flatten (pieceSize pieces xs) xs, List.mem_flatten] at hx
  obtain ⟨part, hpart, hxpart⟩ := hx
  exact List.all_eq_true.mp (h part hpart) x hxpart

-- The pieces of a list put back together give the list.
#guard (chunksOf 3 [1, 2, 3, 4, 5, 6, 7]) == [[1, 2, 3], [4, 5, 6], [7]]
#guard parallelMap (· * 2) (List.range 100) 7 == (List.range 100).map (· * 2)
#guard parallelAll (· < 100) (List.range 100) 7 && !parallelAll (· < 99) (List.range 100) 7

end Rpg.Probability
