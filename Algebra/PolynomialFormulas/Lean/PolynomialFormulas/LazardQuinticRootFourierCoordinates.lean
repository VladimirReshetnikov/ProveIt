import PolynomialFormulas.LazardQuintic

/-!
# Lightweight root Fourier coordinates

This module contains only the four positive Fourier coordinates of an ordered
five-tuple and the two orbit orderings used by Lazard's projection formulas.
It deliberately has no dependency on elementary-symmetric coefficient data.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

/-- The positive-exponent Fourier sum `P₁`. -/
def rootFourierP1 {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  x 0 + omega.value * x 1 + omega.value ^ 2 * x 2 +
    omega.value ^ 3 * x 3 + omega.value ^ 4 * x 4

/-- The positive-exponent Fourier sum `P₂`. -/
def rootFourierP2 {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  x 0 + omega.value ^ 2 * x 1 + omega.value ^ 4 * x 2 +
    omega.value * x 3 + omega.value ^ 3 * x 4

/-- The positive-exponent Fourier sum `P₃`. -/
def rootFourierP3 {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  x 0 + omega.value ^ 3 * x 1 + omega.value * x 2 +
    omega.value ^ 4 * x 3 + omega.value ^ 2 * x 4

/-- The positive-exponent Fourier sum `P₄`. -/
def rootFourierP4 {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K :=
  x 0 + omega.value ^ 4 * x 1 + omega.value ^ 3 * x 2 +
    omega.value ^ 2 * x 3 + omega.value * x 4

/-- The four positive Fourier components in the orbit order
`P₁,P₂,P₄,P₃`. -/
def rootFourierOrbit {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  ![rootFourierP1 omega x, rootFourierP2 omega x,
    rootFourierP4 omega x, rootFourierP3 omega x]

/-- The four conjugate fifth powers in the order used by Lazard's standard
projection matrix. -/
def rootFourierFifthOrbit {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  ![rootFourierP1 omega x ^ 5, rootFourierP2 omega x ^ 5,
    rootFourierP4 omega x ^ 5, rootFourierP3 omega x ^ 5]

/-- The fifth-power orbit is pointwise the fifth power of
`rootFourierOrbit`. -/
theorem rootFourierFifthOrbit_eq_fifth_power_source
    {K : Type*} [CommRing K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierFifthOrbit omega x =
      fun j => rootFourierOrbit omega x j ^ 5 := by
  funext j
  fin_cases j <;> rfl

end LeanProofs.PolynomialFormulas.LazardQuintic
