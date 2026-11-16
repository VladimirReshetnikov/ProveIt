module
public import PA196.Arithmetic.CommandInternal
@[expose] public section

namespace PA196.Arithmetic.CommandStep
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA M6.PA.SourceCantorInternal HeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact safe region for an individual Shift summand. -/
def Sparse (x : V) : Prop := x = 0 ∨ 2 ≤ x

theorem sparse_four_mul (p : V) : Sparse (4 * p) := by
  by_cases hp : p = 0
  · simp [Sparse, hp]
  · have hone : (1 : V) ≤ p := one_le_of_zero_lt p (pos_iff_ne_zero.mpr hp)
    have hfour : (4 : V) ≤ 4 * p := by
      simpa using mul_le_mul_of_nonneg_left hone (show (0 : V) ≤ 4 by simp)
    have h24 : (2 : V) ≤ 4 := calc
      (2 : V) ≤ 2 + 1 := le_add_of_nonneg_right (by simp)
      _ ≤ (2 + 1) + 1 := le_add_of_nonneg_right (by simp)
      _ = 4 := by rw [two_add_one_eq_three, three_add_one_eq_four]
    exact Or.inr (le_trans h24 hfour)

theorem sparse_ne_one {x : V} (hx : Sparse x) : x ≠ 1 := by
  rcases hx with rfl | hx
  · simp
  · exact ne_of_gt (lt_of_lt_of_le (show (1 : V) < 2 by simp) hx)

theorem sparse_add_ne_one {x y : V} (hx : Sparse x) (hy : Sparse y) : x + y ≠ 1 := by
  rcases hx with rfl | hx
  · simpa using sparse_ne_one hy
  · exact ne_of_gt (lt_of_lt_of_le (show (1 : V) < 2 by simp) (le_trans hx (by simp)))

theorem universal_ge_two (a b : V) :
    2 ≤ ActualArithmeticGraph.eval universalExpr a b 0 0 := by
  simp [universalExpr, al, im, ActualArithmeticGraph.eval]

theorem universal_add_ne_one (a b t : V) :
    ActualArithmeticGraph.eval universalExpr a b 0 0 + t ≠ 1 :=
  ne_of_gt (lt_of_lt_of_le (show (1 : V) < 2 by simp)
    (le_trans (universal_ge_two a b) (by simp)))

theorem schemaHeads_sparse (D H A d h : V) :
    ∀ z ∈ schemaHeads D H A d h, Sparse z := by
  intro z hz
  simp only [schemaHeads, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inr (universal_ge_two d h)
    | (simp only [head1Expr, head2Expr, head3Expr, head4Expr, head5Expr,
        head6Expr, rho8Expr, ex, neg, im, ActualArithmeticGraph.eval, Nat.cast_ofNat]
       exact sparse_four_mul _)

theorem gate_sparse (a b c d : V) : Sparse (gateValue a b c d) := by
  unfold gateValue
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · simp only [bundleExpr, neg, im, ActualArithmeticGraph.eval, Nat.cast_ofNat]
      exact sparse_four_mul _

theorem four_mul_ne_four_mul_add_two (a b : V) : 4 * a ≠ 4 * b + 2 := by
  have h24 : (2 : V) < 4 := calc
    (2 : V) < 2 + 1 := by simp
    _ ≤ (2 + 1) + 1 := le_add_of_nonneg_right (by simp)
    _ = 4 := by rw [two_add_one_eq_three, three_add_one_eq_four]
  rcases le_or_gt a b with hab | hba
  · have hm := mul_le_mul_of_nonneg_left hab (show (0 : V) ≤ 4 by simp)
    exact ne_of_lt (lt_of_le_of_lt hm (by simp))
  · have hm := mul_le_mul_of_nonneg_left (succ_le_iff_lt.mpr hba) (show (0 : V) ≤ 4 by simp)
    have hh : 4 * b + 4 ≤ 4 * a := by simpa only [mul_add, mul_one] using hm
    have hl : 4 * b + 2 < 4 * b + 4 := by
      simpa only [add_comm] using add_lt_add_left h24 (4 * b)
    exact ne_of_gt (lt_of_lt_of_le hl hh)

theorem implication_ne_universal (a b c d : V) :
    ActualArithmeticGraph.eval implicationExpr a b 0 0 ≠
      ActualArithmeticGraph.eval universalExpr c d 0 0 := by
  simpa [implicationExpr, universalExpr, im, al, ActualArithmeticGraph.eval] using
    four_mul_ne_four_mul_add_two (pairValue a b) (pairValue d c)

theorem source_pair_eq_zero (a b : V) : pairValue a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hh
    have h0 : pairValue (0 : V) 0 = 0 := by simp [pairValue]
    exact pairValue_injective (hh.trans h0.symm)
  · rintro ⟨rfl, rfl⟩
    simp [pairValue]

theorem implication_eq_zero (a b : V) :
    ActualArithmeticGraph.eval implicationExpr a b 0 0 = 0 ↔ a = 0 ∧ b = 0 := by
  simp [implicationExpr, im, ActualArithmeticGraph.eval, source_pair_eq_zero]

#print axioms schemaHeads_sparse
#print axioms implication_ne_universal
end PA196.Arithmetic.CommandStep
