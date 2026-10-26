import Init

namespace ProofSimplification20261026

/-- Core-only audit of the bounded-complement cancellation used by the
mathlib `tsub_right_inj` integration. The two bounds are essential. -/
theorem boundedComplementRecover {cap a b : Nat}
    (ha : a < cap + 1) (hb : b < cap + 1)
    (h : cap - a = cap - b) : a = b :=
  (Nat.sub_sub_self (Nat.le_of_lt_succ ha)).symm.trans
    ((congrArg (fun v => cap - v) h).trans
      (Nat.sub_sub_self (Nat.le_of_lt_succ hb)))

/-- This shows why unguarded cancellation would be false. -/
example : 255 - 256 = 255 - 257 ∧ (256 : Nat) ≠ 257 := by decide

#print axioms boundedComplementRecover

end ProofSimplification20261026
