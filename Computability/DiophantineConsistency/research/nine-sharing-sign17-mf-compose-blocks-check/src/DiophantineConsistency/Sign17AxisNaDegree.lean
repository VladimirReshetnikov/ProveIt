import DiophantineConsistency.Sign17AxisBindingRoot

/-! SOURCE-ONLY: degree of the actual staged Na residual on the chosen axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisNaDegree
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale Sign17AxisRootBinding

theorem row06_axis (p : Fin 4 → ℤ) :
    (row06 p).evalRing axis =
      (shift * shift - (scale (p 0) * scale (p 0)) * (shift * shift)) - 1 := by
  simp only [row06, shared34, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    shared33_axis, axis13, axis17, Int.cast_one, shift, mul_zero, sub_zero]
  all_goals rfl

theorem row06_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    ((row06 p).evalRing axis).natDegree = 48 := by
  have hf : (shift * shift).natDegree = 2 := by
    simpa using degree_product shift shift 1 1 shift_degree shift_degree (by decide) (by decide)
  have hs : (scale (p 0) * scale (p 0)).natDegree = 46 := by
    simpa using degree_product (scale (p 0)) (scale (p 0)) 23 23
      (scale_degree (p 0) hz) (scale_degree (p 0) hz) (by decide) (by decide)
  have hh : ((scale (p 0) * scale (p 0)) * (shift * shift)).natDegree = 48 := by
    simpa using degree_product (scale (p 0) * scale (p 0)) (shift * shift) 46 2
      hs hf (by decide) (by decide)
  have hd : (shift * shift - (scale (p 0) * scale (p 0)) * (shift * shift)).natDegree = 48 := by
    calc
      (shift * shift - (scale (p 0) * scale (p 0)) * (shift * shift)).natDegree =
          ((scale (p 0) * scale (p 0)) * (shift * shift)).natDegree :=
        Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by omega)
      _ = 48 := hh
  rw [row06_axis]
  calc
    (shift * shift - (scale (p 0) * scale (p 0)) * (shift * shift) - 1).natDegree =
        (shift * shift - (scale (p 0) * scale (p 0)) * (shift * shift)).natDegree :=
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp [hd])
    _ = 48 := hd

end DiophantineConsistency.Sign17AxisNaDegree
#print axioms DiophantineConsistency.Sign17AxisNaDegree.row06_axis
#print axioms DiophantineConsistency.Sign17AxisNaDegree.row06_axis_degree
