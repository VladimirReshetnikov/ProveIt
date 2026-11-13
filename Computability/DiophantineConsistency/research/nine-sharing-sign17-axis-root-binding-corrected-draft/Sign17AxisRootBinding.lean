import DiophantineConsistency.Sign17AxisDegreeScale

/-! SOURCE-ONLY: connect the explicit axis root and scale to staged syntax. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisRootBinding
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale

def axis (i : Fin 18) : P := if i = 0 then 1 else if i = 17 then 0 else Polynomial.X

theorem axis01 : axis 1 = Polynomial.X := rfl
theorem axis06 : axis 6 = Polynomial.X := rfl
theorem axis08 : axis 8 = Polynomial.X := rfl
theorem axis09 : axis 9 = Polynomial.X := rfl
theorem axis11 : axis 11 = Polynomial.X := rfl
theorem axis12 : axis 12 = Polynomial.X := rfl
theorem axis13 : axis 13 = Polynomial.X := rfl
theorem axis14 : axis 14 = Polynomial.X := rfl
theorem axis17 : axis 17 = 0 := rfl
theorem axis00 : axis 0 = 1 := rfl

theorem shared07_axis (p : Fin 4 → ℤ) :
    (shared07 p).evalRing axis = low (p 0) := by
  simp only [shared07, shared02, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis09,
    low, affine, shift, Polynomial.C_eq_intCast, Int.cast_one]
  ring

theorem shared26_axis (p : Fin 4 → ℤ) :
    (shared26 p).evalRing axis = dominant (p 0) := by
  simp only [shared26, shared20, shared18, shared05, shared13, shared12,
    shared08, shared17, shared16, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis08, axis09, axis11, axis12,
    dominant, e, y, cube, u, twice, affine, shift,
    Polynomial.C_eq_intCast, Int.cast_ofNat, Int.cast_one]
  ring

theorem shared24_axis (p : Fin 4 → ℤ) :
    (shared24 p).evalRing axis = middle (p 0) := by
  simp only [shared24, shared22, shared21, shared20, shared18, shared05,
    shared13, shared12, shared08, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis08, axis09, axis14,
    middle, e, y, cube, affine, shift,
    Polynomial.C_eq_intCast, Int.cast_ofNat, Int.cast_one]
  ring

theorem shared29_axis (p : Fin 4 → ℤ) :
    (shared29 p).evalRing axis = root (p 0) := by
  simp only [shared29, shared27, Expr.evalRing_add, shared07_axis,
    shared26_axis, shared24_axis, root]

theorem shared33_axis (p : Fin 4 → ℤ) :
    (shared33 p).evalRing axis = scale (p 0) := by
  simp only [shared33, shared32, shared30, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, shared29_axis, axis06,
    Int.cast_ofNat, Int.cast_one, scale, shift]
  ring

end DiophantineConsistency.Sign17AxisRootBinding
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared07_axis
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared26_axis
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared24_axis
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared29_axis
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared33_axis
