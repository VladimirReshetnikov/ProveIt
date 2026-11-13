import MaskCoordinate79
import Mask79Carrier

/-! Factor the actual 79 core into unchanged shared rows and the main carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mask79ActualRows
open DiophantineConsistency AdaptiveEquationSyntax2011 TenPositive79Mask
variable {R : Type*} [CommRing R]

structure Shared (R : Type*) where
  b q k w sq u H Z P L T : R

def shared (p : Fin 4 → ℤ) (v : Fin 10 → R) (G : R) : Shared R :=
  let t01 : R := (p 0:R) * (v 0)
  let t02 : R := t01 + ((1:ℤ):R)
  let t03 : R := t02 * t02
  let t04 : R := t03 * t02
  let t05 : R := t04 * (v 6)
  let t07 : R := (v 5) * t02
  let t08 : R := (v 8) + (v 9)
  let t09 : R := t08 * t05
  let t10 : R := t09 + (v 8)
  let t11 : R := t03 + ((1:ℤ):R)
  let t12 : R := t07 + ((1:ℤ):R)
  let t13 : R := t11 * t05
  let t14 : R := t13 * t12
  let t15 : R := ((4:ℤ):R) * t14
  let t16 : R := t15 - ((1:ℤ):R)
  let t17 : R := t14 + ((2:ℤ):R)
  let t18 : R := t13 * t13
  let t19 : R := t07 * t18
  let t20 : R := t19 * t08
  let t21 : R := t20 + t08
  let t22 : R := t20 * t21
  let t23 : R := t22 + ((1:ℤ):R)
  let t24 : R := t03 - ((1:ℤ):R)
  let t25 : R := G * t24
  let t26 : R := t02 * (p 3:R)
  let t27 : R := (p 2:R) + t26
  let t28 : R := t27 * (v 0)
  let t29 : R := t25 + t28
  let t30 : R := t08 - t29
  let t31 : R := t30 - ((1:ℤ):R)
  let t32 : R := (p 1:R) + (v 5)
  let t35 : R := t10 * t10
  let t36 : R := (v 3) * t35
  let t37 : R := t36 * t23
  let t38 : R := t14 * t17
  let t39 : R := t38 * t37
  let t40 : R := t39 * t36
  let t41 : R := t40 + ((1:ℤ):R)
  let t42 : R := t40 * t41
  let t43 : R := ((4:ℤ):R) * t42
  let t44 : R := t43 + ((1:ℤ):R)
  let t45 : R := t38 * t43
  let t46 : R := t10 * (v 4)
  let t47 : R := t46 - t29
  let t48 : R := t44 * t47
  let t49 : R := t48 - t10
  let t50 : R := t49 * t49
  let t51 : R := t11 * t11
  let t52 : R := t01 * t51
  let t56 : R := ((3:ℤ):R) * t10
  let t57 : R := ((2:ℤ):R) * t07
  let t58 : R := t56 - t57
  let t59 : R := t07 * t58
  let t60 : R := t59 + ((2:ℤ):R)
  let t68 : R := t52 * t16
  let t69 : R := t68 * t68
  let t70 : R := t23 * t41
  { b := t01, q := t02, k := (p 1:R), w := v 5, sq := t50, u := t51,
    H := t16, Z := t60, P := t31, L := t45, T := t69*t70 }

def main (s : Shared R) (F C n : R) : R :=
  let B := (s.k+s.w)*C-F
  (s.b*s.u)*(s.H*(n-s.sq*B)+s.Z)-s.H*(s.u*B+s.b*s.P)

def output (s : Shared R) (F C n : R) : R :=
  let m := main s F C n
  s.L*(m*m-s.T*s.sq)+(s.T-m*m)

theorem core_decompose (p : Fin 4 → ℤ) (v : Fin 10 → R) (C G : R) :
    core p v C G = output (shared p v G) (v 1) C (v 7) := by
  rfl

#print axioms Mask79ActualRows.core_decompose
end Mask79ActualRows
