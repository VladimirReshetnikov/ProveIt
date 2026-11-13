import DiophantineConsistency.Sign14AxisBindingRoot

/-! SOURCE-ONLY: bind the retained correction/rank and substituted inner. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisInnerBinding
open SharingSeed14Degree124 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale Sign14AxisBinding
  Sign14AxisGenericDegree Sign14SyntaxDegree

attribute [local irreducible] shared14 shared27

theorem axis05 : axis 5 = Polynomial.X := rfl
theorem axis07 : axis 7 = Polynomial.X := rfl

theorem eval_degree_le {σ : Type} (e : Expr σ) (v : σ → P)
    (hv : ∀ i, (v i).natDegree ≤ 1) : (e.evalRing v).natDegree ≤ degree e := by
  induction e with
  | constant z => simp [Expr.evalRing, degree]
  | var i => simpa [Expr.evalRing, degree] using hv i
  | add a b ha hb => exact (Polynomial.natDegree_add_le _ _).trans (max_le_max ha hb)
  | sub a b ha hb => exact (Polynomial.natDegree_sub_le _ _).trans (max_le_max ha hb)
  | mul a b ha hb => exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add ha hb)

theorem axis_degree_le (i : Fin 15) : (axis i).natDegree ≤ 1 := by
  by_cases h : i = 0 <;> simp [axis, h]

theorem correction_degree (p : Fin 4 → ℤ) :
    ((shared14 p).evalRing axis).natDegree ≤ 2 :=
  (eval_degree_le (shared14 p) axis axis_degree_le).trans (shared14_degree p)

theorem rank_degree (p : Fin 4 → ℤ) :
    ((shared27 p).evalRing axis).natDegree ≤ 4 :=
  (eval_degree_le (shared27 p) axis axis_degree_le).trans (shared27_degree p)

theorem shared17_axis (p : Fin 4 → ℤ) : (shared17 p).evalRing axis = u (p 0) := by
  simp only [shared17, shared16, shared13, shared12, shared08,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    axis01, axis08, axis11, axis12, u, twice, y, cube, affine, shift,
    polynomial_C_eq_cast, Int.cast_ofNat, Int.cast_one, two_mul, mul_assoc]
  all_goals rfl

theorem shared37_axis (p : Fin 4 → ℤ) :
    (shared37 p).evalRing axis = inner (p 0) ((shared14 p).evalRing axis)
      ((shared27 p).evalRing axis) := by
  simp only [shared37, shared35, shared34, shared25, shared19,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, shared17_axis,
    axis05, axis07, Int.cast_one, inner, shift]
  ring

theorem shared37_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    ((shared37 p).evalRing axis).natDegree = 8 := by
  rw [shared37_axis]
  exact inner_degree (p 0) hz _ _ (correction_degree p) (rank_degree p)
end DiophantineConsistency.Sign14AxisInnerBinding
#print axioms DiophantineConsistency.Sign14AxisInnerBinding.correction_degree
#print axioms DiophantineConsistency.Sign14AxisInnerBinding.rank_degree
#print axioms DiophantineConsistency.Sign14AxisInnerBinding.shared17_axis
#print axioms DiophantineConsistency.Sign14AxisInnerBinding.shared37_axis
#print axioms DiophantineConsistency.Sign14AxisInnerBinding.shared37_axis_degree
