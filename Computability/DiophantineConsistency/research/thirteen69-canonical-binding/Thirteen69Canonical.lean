import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ThirteenCarrier

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Thirteen69Canonical
open DiophantineConsistency
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing

def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let s : Expr (Fin 13) := .var 6
  let w : Expr (Fin 13) := .var 7
  let n : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let m : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let beta : Expr (Fin 13) := .constant (p 0)
  let K : Expr (Fin 13) := .constant (p 1)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
  let b := beta * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) + (MC + q * MF) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let G := (K + w) * C - F
  let y := 1 + 4 * (b * (m - V ^ 2 * G) - G)
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let t := b * i * c ^ 2
  let S := delta * t
  P * Q * (S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2) * (delta * f ^ 2 - S ^ 2) - delta

theorem eval_literal {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (literal p).evalRing v = ThirteenCarrier.value69 (fun j => (p j : R)) v := by
  simp only [literal, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_pow,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Nat.cast_ofNat, Nat.cast_one, ThirteenCarrier.value69, ThirteenCarrier.core]

section Model
variable {V : Type*} [CommSemiring V] [LinearOrder V] [IsStrictOrderedRing V]
  [CanonicallyOrderedAdd V]

theorem internal_zero (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (literal p) v ↔
      ThirteenCarrier.value69 (fun j => (p j : DiffRing V)) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff, eval_literal]

theorem shifted_zero (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (positiveShift (literal p)) v ↔
      ThirteenCarrier.value69 (fun j => (p j : DiffRing V)) (fun j => ι (v j + 1)) = 0 := by
  rw [internalZero_positiveShift, internal_zero]

def currentLiteral : Expr (Fin 13) := positiveShift (literal CurrentWindowCarry2011.ports)

theorem current_zero (v : Fin 13 → V) :
    InternalZero currentLiteral v ↔
      ThirteenCarrier.value69 (fun j => (CurrentWindowCarry2011.ports j : DiffRing V))
        (fun j => ι (v j + 1)) = 0 := shifted_zero _ v
end Model
end Thirteen69Canonical
#print axioms Thirteen69Canonical.eval_literal
#print axioms Thirteen69Canonical.internal_zero
#print axioms Thirteen69Canonical.shifted_zero
#print axioms Thirteen69Canonical.current_zero
