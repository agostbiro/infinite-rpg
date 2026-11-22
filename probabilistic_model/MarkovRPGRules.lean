import Mathlib.Data.Nat.Basic

namespace MarkovRPG.Combat

/-- One common rulebook for every character and combat in the game. -/
structure Rules where
  hpMax : Nat := 20
  hpMax_pos : 0 < hpMax := by decide
  attributeMax : Nat := 20
  skillMax : Nat := 30
  protectionMax : Nat := 40
  damageMax : Nat := 100
  diceMax : Nat := 8
  modifierMax : Nat := 20
  itemSlots : Nat := 8
  effectsPerSource : Nat := 8
  stockMax : Nat := 9
  durationMax : Nat := 10
  resourceMax : Nat := 99
  defenseBonus : Nat := 2
  minimumRollLevel : Int := 3
  halveDodgeBelowThird : Bool := true

end MarkovRPG.Combat
