import Energy

namespace IPRAIntegration

/-- The invalid independent-tail shortcut fails even at one rational atom. -/
def tailUnion (K x y : Rat) : Rat :=
  if K < x.abs ∨ K < y.abs then (x - y).abs else 0

theorem independent_tail_shortcut_false :
    ¬ tailUnion 1 2 (-1) ≤ tail 1 2 + tail 1 (-1) := by
  simp only [tailUnion, tail, Rat.abs]
  repeat' split
  all_goals grind

example : clip 1 2 = 1 := by
  simp only [clip]
  repeat' split
  all_goals grind
example : clip 1 (-1) = -1 := by
  simp only [clip]
  repeat' split
  all_goals grind
example : excess 1 2 = 1 := by
  simp only [excess, Rat.abs]
  repeat' split
  all_goals grind
example : excess 1 (-1) = 0 := by
  simp only [excess, Rat.abs]
  repeat' split
  all_goals grind
example : rho 2 (-1) = 1 := by
  simp only [rho, Rat.abs]
  repeat' split
  all_goals grind
example : detail2 3 1 = 1 := by unfold detail2; grind
example : mean2 3 1 = 2 := by unfold mean2; grind
example : smallWindow (fun n => (min n 3 : Nat)) 1 4 = some 3 := by
  change (if (3 : Rat) ≤ 3 + 1 then some 3 else _) = some 3
  have h : (3 : Rat) ≤ 3 + 1 := by grind
  rw [if_pos h]

end IPRAIntegration
