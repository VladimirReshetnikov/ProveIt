import DiophantineConsistency.Compact44.FreeJSumSquares
import Mathlib.Tactic.LinearCombination

/-! # Package 57's 12-positive, 89-operation equation of degree 258

`57-separated-degrees/low_degree/twelve_positive_degree258.json`, the
full-modulus variant of the package's §9. It has twelve positive inputs
`J F α z i T s w η ζ y t` and the four compact44 ports. With `q = βJ + 1`,
`X = wq`, `Y = sq³`, `U = 4q⁴` and `S = UH`, the equation is
`Nt·(1 + N)·(1 + J_M) − 1 = 0`, where:

* `Nt = (K0 + w)C + (q − F) − z(q−1)`, the transport;
* `N = (W² + U²G − S²A)² − 4W²·U²G`, with
  `W = U(X + ac) + H(U(t + ℓ) + (k − R − 1))`, `G = Δc² + 1` and
  `A = ℓ(ℓ+k) + 1`. This fuses the main and first carriers;
* `J_M = Z² − 4Dv²b²`, with `I = ic²`, `Q = (ΔI)²`, `D = ΔI·I + 1`, `v = cT`,
  `b = c + RD` and `Z = (Dv² + b² − 1) + (Q − 1)y(2 − Qy)`. This fuses the
  normalized strong and auxiliary norms.

The gate block is generated from the pinned JSON by
`research/twelve-p57-endpoint/tools/generate_p57.py`, which also checks it.
This module evaluates every factor in an arbitrary commutative ring as a field
of `vals`, a gate-by-gate record of the registers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P57Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  Nt : Expr (Fin 12)
  N : Expr (Fin 12)
  inner : Expr (Fin 12)
  output : Expr (Fin 12)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 12) := .var 0
  let F : Expr (Fin 12) := .var 1
  let alpha : Expr (Fin 12) := .var 2
  let z : Expr (Fin 12) := .var 3
  let i : Expr (Fin 12) := .var 4
  let T : Expr (Fin 12) := .var 5
  let s : Expr (Fin 12) := .var 6
  let w : Expr (Fin 12) := .var 7
  let eta : Expr (Fin 12) := .var 8
  let zeta : Expr (Fin 12) := .var 9
  let y : Expr (Fin 12) := .var 10
  let t : Expr (Fin 12) := .var 11
  let beta : Expr (Fin 12) := .constant (p 0)
  let K0 : Expr (Fin 12) := .constant (p 1)
  let MC : Expr (Fin 12) := .constant (p 2)
  let MF : Expr (Fin 12) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let qm := beta * J
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let q4 := q2 * q2
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let c := kY + eta
  let c2 := c * c
  let a := E + Y
  let r13 := 4 * a
  let H := r13 + 3
  let r15 := a * a
  let Delta := r15 + H
  let ell := E * kY
  let r18 := ell + k
  let r19 := ell * r18
  let A := r19 + 1
  let r21 := Delta * c2
  let G := r21 + 1
  let r23 := a * c
  let b0 := X + r23
  let qF := q - F
  let C := qF - alpha
  let r27 := qm * qF
  let r28 := r27 + alpha
  let r29 := q2 - 1
  let r30 := r28 * r29
  let r31 := q * MF
  let r32 := MC + r31
  let r33 := r32 * J
  let R := r30 + r33
  let r35 := K0 + w
  let r36 := r35 * C
  let r37 := r36 + qF
  let r38 := z * qm
  let Nt := r37 - r38
  let U := 4 * q4
  let r41 := k - R
  let r := r41 - 1
  let S := U * H
  let r44 := U * b0
  let r45 := t + ell
  let r46 := U * r45
  let r47 := r46 + r
  let r48 := H * r47
  let W := r44 + r48
  let W2 := W * W
  let r51 := U * U
  let UG := r51 * G
  let r53 := S * S
  let SA := r53 * A
  let r55 := W2 + UG
  let r56 := r55 - SA
  let r57 := r56 * r56
  let r58 := W2 * UG
  let r59 := 4 * r58
  let N := r57 - r59
  let I := i * c2
  let DI := Delta * I
  let Q := DI * DI
  let r64 := DI * I
  let D := r64 + 1
  let daux := Q - 1
  let v := c * T
  let r68 := R * D
  let baux := c + r68
  let r70 := v * v
  let Dv2 := D * r70
  let b2 := baux * baux
  let r73 := Dv2 + b2
  let r74 := r73 - 1
  let r75 := daux * y
  let r76 := Q * y
  let r77 := 2 - r76
  let r78 := r75 * r77
  let innerbase := r74 + r78
  let r80 := innerbase * innerbase
  let r81 := Dv2 * b2
  let r82 := 4 * r81
  let inner := r80 - r82
  let r84 := N + 1
  let r85 := Nt * r84
  let r86 := inner + 1
  let r87 := r85 * r86
  let out := r87 - 1
  -- END LITERAL GRAPH
  ⟨Nt, N, inner, out⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).Nt * ((graph p).N + 1) * ((graph p).inner + 1) - 1 := by
  rfl

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values, gate by gate. -/
structure Vals (R : Type*) where
  qm : R
  q : R
  U : R
  X : R
  Y : R
  E : R
  k : R
  c : R
  a : R
  H : R
  Delta : R
  ell : R
  A : R
  G : R
  b0 : R
  qF : R
  Cw : R
  RR : R
  Nt : R
  S : R
  W : R
  N : R
  I : R
  Q : R
  D : R
  v : R
  baux : R
  Z : R
  inner : R

def vals (p : Fin 4 → ℤ) (w : Fin 12 → R) : Vals R :=
  let qm := (p 0 : R) * w 0
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let q4 := q2 * q2
  let X := w 7 * q
  let Y := w 6 * q3
  let E := X * Y
  let k := w 8 + w 9
  let kY := k * Y
  let c := kY + w 8
  let c2 := c * c
  let a := E + Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let ell := E * kY
  let A := ell * (ell + k) + 1
  let G := Delta * c2 + 1
  let b0 := X + a * c
  let qF := q - w 1
  let Cw := qF - w 2
  let RR := (qm * qF + w 2) * (q2 - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0
  let Nt := (((p 1 : R) + w 7) * Cw + qF) - w 3 * qm
  let U := 4 * q4
  let S := U * H
  let W := U * b0 + H * (U * (w 11 + ell) + ((k - RR) - 1))
  let N := ((W * W + (U * U) * G) - (S * S) * A) * ((W * W + (U * U) * G) - (S * S) * A) -
    4 * ((W * W) * ((U * U) * G))
  let I := w 4 * c2
  let DI := Delta * I
  let Q := DI * DI
  let D := DI * I + 1
  let v := c * w 5
  let baux := c + RR * D
  let Dv2 := D * (v * v)
  let b2 := baux * baux
  let Z := ((Dv2 + b2) - 1) + ((Q - 1) * w 10) * (2 - Q * w 10)
  let inner := Z * Z - 4 * (Dv2 * b2)
  ⟨qm, q, U, X, Y, E, k, c, a, H, Delta, ell, A, G, b0, qF, Cw, RR, Nt, S, W, N, I, Q, D, v, baux,
    Z, inner⟩

theorem Nt_eval (p : Fin 4 → ℤ) (w : Fin 12 → R) : (graph p).Nt.evalRing w = (vals p w).Nt := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem N_eval (p : Fin 4 → ℤ) (w : Fin 12 → R) : (graph p).N.evalRing w = (vals p w).N := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem inner_eval (p : Fin 4 → ℤ) (w : Fin 12 → R) :
    (graph p).inner.evalRing w = (vals p w).inner := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem output_eval (p : Fin 4 → ℤ) (w : Fin 12 → R) :
    (graph p).output.evalRing w =
      (vals p w).Nt * ((vals p w).N + 1) * ((vals p w).inner + 1) - 1 := by
  rw [output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Nat.cast_one]
  rw [Nt_eval, N_eval, inner_eval]

end Ring

end P57Graph

#print axioms P57Graph.output_eq
#print axioms P57Graph.Nt_eval
#print axioms P57Graph.N_eval
#print axioms P57Graph.inner_eval
#print axioms P57Graph.output_eval
