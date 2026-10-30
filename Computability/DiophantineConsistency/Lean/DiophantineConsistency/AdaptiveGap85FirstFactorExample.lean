import DiophantineConsistency.AdaptiveGap85Literal

/-! A small artificial-parameter example for only two factor units. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace DiophantineConsistency.AdaptiveGap85FirstFactorExample
open AdaptiveGap85Literal

def ports : Fin 4 → ℤ := ![1,2,0,0]
def witness : Fin 13 → ℤ := ![1,2,2,1,1,1,1,8,16,1,1,1,1]

def firstFactor : ℤ :=
  let J : ℤ := witness 0
  let F : ℤ := witness 1
  let C : ℤ := witness 2
  let X : ℤ := witness 6
  let Y : ℤ := witness 7
  let r : ℤ := witness 8
  let eta : ℤ := witness 9
  let zeta : ℤ := witness 10
  let b := J*ports 0
  let q := 1+b
  let k := eta+zeta
  let ell := (X*Y)*(Y*k)
  let M := q^3*b
  let W := C*(X+ports 1*q)-F*q
  let Z := M*(ell+k+r-k*W)+Y*b-W*q^3
  1+Z^2-M^2*(1+ell*(ell+k))

def auxiliaryFactor : ℤ :=
  let f : ℤ := witness 3
  let T : ℤ := witness 5
  let X : ℤ := witness 6
  let Y : ℤ := witness 7
  let eta : ℤ := witness 9
  let zeta : ℤ := witness 10
  let y : ℤ := witness 11
  let b := witness 0*ports 0
  let q := 1+b
  let a := X*Y+Y
  let Delta := 3+4*a+a^2
  let c := eta+Y*(eta+zeta)
  let R := ((q-witness 1)*q-witness 2)*(q^2-1)+witness 0*(ports 2+ports 3*q)
  let Q := Delta*(f^2-1)
  let V := f^2*(T*c-R)-c
  y^2-Q*(y^2-V^2)

theorem first_factor_is_one : firstFactor=1 := by decide
theorem auxiliary_factor_is_one : auxiliaryFactor=1 := by decide
theorem reverse_bound_fails : ¬(witness 1+witness 2 < 1+witness 0*ports 0) := by decide
/-- The exact full candidate polynomial is nonzero at this example. -/
theorem full_polynomial_value : (expressionAt85 ports).eval witness=3029421283635 := by decide
end DiophantineConsistency.AdaptiveGap85FirstFactorExample
