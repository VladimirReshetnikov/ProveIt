import DiophantineConsistency.Compact44.FreeJSumSquares
import Mathlib.Tactic.LinearCombination

/-! # Package 62's 13-positive, 83-operation equation of degree 114

`62-sign-and-norm/positive13/polynomial.json`: thirteen positive inputs
`J F α z f i T s w η ζ γ t` and the four compact44 ports. With `q = βJ + 1`,
`X = wq`, `Y = sq³`, `U = 4q⁴` and `C = q − F − α`, the equation is
`Nt·(1 + Nmain)·Ns·(1 + N) − 1 = 0`, where:

* `Nt = (K0 + w)C + (q − F) − z(q−1)`, the transport;
* `Nmain = D*² − U²(Δc² + 1)` with `D* = U(X + ac) + H(Uγ − (k − R − 1))`;
* `Ns = I² − (Q − 1)` with `I = ic²` and `Q = Δ(f²−1)`, the strong norm;
* `N = (dδ − E)² − 4dA·E`, the centered two-root norm. Here `d = Q − 1`,
  `δ = (t + ℓ)² − A` with `A = ℓ(ℓ+k) + 1`, and `E = QV² − 1` with
  `V = c(Tf − 1) − Rf²`, the ordinary-blank auxiliary ordinate.

The gate block is generated from the pinned JSON by
`research/thirteen-p62-endpoint/tools/generate_p62.py`, which also checks it.
This module evaluates every factor in an arbitrary commutative ring as a field
of `vals`, a gate-by-gate record of the registers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P62Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  Nt : Expr (Fin 13)
  Nmain : Expr (Fin 13)
  Ns : Expr (Fin 13)
  N : Expr (Fin 13)
  output : Expr (Fin 13)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let z : Expr (Fin 13) := .var 3
  let f : Expr (Fin 13) := .var 4
  let i : Expr (Fin 13) := .var 5
  let T : Expr (Fin 13) := .var 6
  let s : Expr (Fin 13) := .var 7
  let w : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let gamma : Expr (Fin 13) := .var 11
  let t : Expr (Fin 13) := .var 12
  let beta : Expr (Fin 13) := .constant (p 0)
  let K0 : Expr (Fin 13) := .constant (p 1)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let qm1 := beta * J
  let q := qm1 + 1
  let q2 := q * q
  let q3 := q2 * q
  let q4 := q2 * q2
  let U := 4 * q4
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let c := kY + eta
  let a := E + Y
  let r14 := 4 * a
  let H := r14 + 3
  let r16 := a * a
  let Delta := r16 + H
  let ell := E * kY
  let r19 := ell + k
  let r20 := ell * r19
  let A1 := r20 + 1
  let c2 := c * c
  let r23 := Delta * c2
  let G := r23 + 1
  let r25 := a * c
  let b0 := X + r25
  let qF := q - F
  let Cw := qF - alpha
  let r29 := qm1 * qF
  let r30 := r29 + alpha
  let r31 := q2 - 1
  let r32 := r30 * r31
  let r33 := q * MF
  let r34 := MC + r33
  let r35 := r34 * J
  let R := r32 + r35
  let r37 := K0 + w
  let r38 := r37 * Cw
  let r39 := r38 + qF
  let r40 := z * qm1
  let Nt := r39 - r40
  let r42 := k - R
  let r := r42 - 1
  let r44 := U * b0
  let r45 := U * gamma
  let r46 := r45 - r
  let r47 := H * r46
  let Dstar := r44 + r47
  let r49 := Dstar * Dstar
  let r50 := U * U
  let r51 := r50 * G
  let Nmain := r49 - r51
  let I := i * c2
  let I2 := I * I
  let f2 := f * f
  let r56 := f2 - 1
  let Q := Delta * r56
  let d := Q - 1
  let Ns := I2 - d
  let r60 := T * f
  let r61 := r60 - 1
  let r62 := c * r61
  let r63 := R * f2
  let V := r62 - r63
  let x := t + ell
  let x2 := x * x
  let r67 := V * V
  let r68 := Q * r67
  let Eaux := r68 - 1
  let delta := x2 - A1
  let r71 := d * delta
  let core := r71 - Eaux
  let r73 := core * core
  let r74 := d * A1
  let r75 := r74 * Eaux
  let r76 := 4 * r75
  let N := r73 - r76
  let r78 := Nmain + 1
  let r79 := Nt * r78
  let r80 := r79 * Ns
  let r81 := N + 1
  let r82 := r80 * r81
  let P13 := r82 - 1
  -- END LITERAL GRAPH
  ⟨Nt, Nmain, Ns, N, P13⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).Nt * ((graph p).Nmain + 1) * (graph p).Ns * ((graph p).N + 1) - 1 := by
  rfl

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values, gate by gate. -/
structure Vals (R : Type*) where
  qm : R
  q : R
  q3 : R
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
  A1 : R
  b0 : R
  qF : R
  Cw : R
  RR : R
  Nt : R
  Dstar : R
  Nmain : R
  I : R
  Q : R
  d : R
  Ns : R
  V : R
  x : R
  Eaux : R
  core : R
  N : R

def vals (p : Fin 4 → ℤ) (w : Fin 13 → R) : Vals R :=
  let qm := (p 0 : R) * w 0
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let q4 := q2 * q2
  let U := 4 * q4
  let X := w 8 * q
  let Y := w 7 * q3
  let E := X * Y
  let k := w 9 + w 10
  let kY := k * Y
  let c := kY + w 9
  let a := E + Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let ell := E * kY
  let A1 := ell * (ell + k) + 1
  let c2 := c * c
  let G := Delta * c2 + 1
  let b0 := X + a * c
  let qF := q - w 1
  let Cw := qF - w 2
  let RR := (qm * qF + w 2) * (q2 - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0
  let Nt := (((p 1 : R) + w 8) * Cw + qF) - w 3 * qm
  let r := (k - RR) - 1
  let Dstar := U * b0 + H * (U * w 11 - r)
  let Nmain := Dstar * Dstar - (U * U) * G
  let I := w 5 * c2
  let Q := Delta * (w 4 * w 4 - 1)
  let d := Q - 1
  let Ns := I * I - d
  let VV := c * (w 6 * w 4 - 1) - RR * (w 4 * w 4)
  let x := w 12 + ell
  let Eaux := Q * (VV * VV) - 1
  let core := d * (x * x - A1) - Eaux
  let N := core * core - 4 * ((d * A1) * Eaux)
  ⟨qm, q, q3, U, X, Y, E, k, c, a, H, Delta, ell, A1, b0, qF, Cw, RR, Nt, Dstar, Nmain, I, Q, d, Ns,
    VV, x, Eaux, core, N⟩

theorem Nt_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) : (graph p).Nt.evalRing w = (vals p w).Nt := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nmain_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).Nmain.evalRing w = (vals p w).Nmain := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Ns_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) : (graph p).Ns.evalRing w = (vals p w).Ns := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem N_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) : (graph p).N.evalRing w = (vals p w).N := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem output_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).output.evalRing w =
      (vals p w).Nt * ((vals p w).Nmain + 1) * (vals p w).Ns * ((vals p w).N + 1) - 1 := by
  rw [output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Nat.cast_one]
  rw [Nt_eval, Nmain_eval, Ns_eval, N_eval]

end Ring

end P62Graph

#print axioms P62Graph.output_eq
#print axioms P62Graph.Nt_eval
#print axioms P62Graph.Nmain_eval
#print axioms P62Graph.Ns_eval
#print axioms P62Graph.N_eval
#print axioms P62Graph.output_eval
