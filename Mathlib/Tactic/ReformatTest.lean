import Mathlib.Tactic.Reformat

#reformat
example (a : Nat) (b : Int) : a = a ∧ b = b := by
  refine ?_
  constructor
  · rw [← Nat.add_zero a]; done
  · apply ?_;
    first | assumption | done |
     assumption | trivial
