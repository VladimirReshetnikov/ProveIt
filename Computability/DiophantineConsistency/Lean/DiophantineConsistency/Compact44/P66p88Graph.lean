import DiophantineConsistency.Compact44.P66Vals

/-! # Package 66's 15-positive, 88-operation equation of degree 24

`66-gap-congruence/algebra/p15_88_degree24.json`: fifteen positive inputs
`j F α z f h i T X Y r η ζ u γ` and the four compact44 ports `β K0 MC MF`; 88
operations, exact degree 24 (package 58's 90-operation `p15_degree24.json` with
`2V + u` computed as `V + (V + u)` and the transport variable shifted, `z = z_old − 1`).
With `J = 3j + 1`, `q = βJ + 1` and `X`, `Y` free, the output is
`A² + B² + index_res² + transport_res² + auxiliary² + strong²`, where (`P66Vals`)

* `A` and `B` as for `P66p87Graph`;
* `index_res = R̂ − R` with `R̂ = (k − hE) − 1`;
* `transport_res = q((K0·C − F) − z(q − 1)) + XC`;
* `auxiliary` as for `P66p78Graph` but at `V = f²(cT − R̂) − c`, and `strong`.

The gate block is generated from the pinned JSON by
`research/fifteen-p66-endpoint/tools/generate_short15_c44.py`, which also checks
it (`--check`) together with the compact44 coefficient binding. This module
proves the sum-of-squares split of zeros and evaluates each residual over an
arbitrary commutative ring through `P66Vals.vals`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P66p88Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing P66Vals

structure Graph where
  A : Expr (Fin 15)
  B : Expr (Fin 15)
  index_res : Expr (Fin 15)
  transport_res : Expr (Fin 15)
  auxiliary : Expr (Fin 15)
  strong : Expr (Fin 15)
  output : Expr (Fin 15)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let j : Expr (Fin 15) := .var 0
  let F : Expr (Fin 15) := .var 1
  let alpha : Expr (Fin 15) := .var 2
  let z : Expr (Fin 15) := .var 3
  let f : Expr (Fin 15) := .var 4
  let h : Expr (Fin 15) := .var 5
  let i : Expr (Fin 15) := .var 6
  let T : Expr (Fin 15) := .var 7
  let X : Expr (Fin 15) := .var 8
  let Y : Expr (Fin 15) := .var 9
  let r : Expr (Fin 15) := .var 10
  let eta : Expr (Fin 15) := .var 11
  let zeta : Expr (Fin 15) := .var 12
  let u : Expr (Fin 15) := .var 13
  let gamma : Expr (Fin 15) := .var 14
  let beta : Expr (Fin 15) := .constant (p 0)
  let K0 : Expr (Fin 15) := .constant (p 1)
  let MC : Expr (Fin 15) := .constant (p 2)
  let MF : Expr (Fin 15) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let triple_j := 3 * j
  let Jold := triple_j + 1
  let qm := beta * Jold
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let q6 := q3 * q3
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let c := kY + eta
  let c2 := c * c
  let a := E + Y
  let four_a := 4 * a
  let H := four_a + 3
  let a2 := a * a
  let Delta := a2 + H
  let ac := a * c
  let gammaH := gamma * H
  let Z := X + gammaH
  let D0 := ac + Z
  let ell := E * kY
  let ell_r := ell + r
  let g25 := q3 * ell_r
  let first_num := g25 + Y
  let g27 := ell + k
  let g28 := ell * g27
  let first_rhs := g28 + 1
  let g30 := first_num * first_num
  let g31 := q6 * first_rhs
  let A := g30 - g31
  let g34 := Delta * c2
  let XH := X * H
  let g37 := q * D0
  let main_num := g37 + XH
  let g39 := main_num * main_num
  let g40 := g34 + 1
  let g41 := q2 * g40
  let B := g39 - g41
  let g43 := qm * qF
  let g44 := g43 + alpha
  let g45 := q2 - 1
  let g46 := g44 * g45
  let g47 := q * MF
  let g48 := MC + g47
  let g49 := g48 * Jold
  let R := g46 + g49
  let g51 := h * E
  let kmhE := k - g51
  let Rhat := kmhE - 1
  let index_res := Rhat - R
  let shift_KC := K0 * C
  let shift_zqm := z * qm
  let shift_t0 := shift_KC - F
  let shift_t1 := shift_t0 - shift_zqm
  let shift_qt := q * shift_t1
  let shift_XC := X * C
  let transport_res := shift_qt + shift_XC
  let f2 := f * f
  let g64 := f2 - 1
  let U := Delta * g64
  let I := i * c2
  let g67 := I * I
  let strong := g67 - U
  let g69 := c * T
  let g70 := g69 - Rhat
  let g71 := f2 * g70
  let V := g71 - c
  let vu := V + u
  let g74 := vu * vu
  let g76 := V + vu
  let g77 := u * g76
  let g78 := U * g77
  let g79 := g74 - g78
  let auxiliary := g79 - 1
  let residual_square_0 := A * A
  let residual_square_1 := B * B
  let residual_square_2 := index_res * index_res
  let residual_square_3 := transport_res * transport_res
  let residual_square_4 := auxiliary * auxiliary
  let residual_square_5 := strong * strong
  let sum_1 := residual_square_0 + residual_square_1
  let sum_2 := sum_1 + residual_square_2
  let sum_3 := sum_2 + residual_square_3
  let sum_4 := sum_3 + residual_square_4
  let sum_5 := sum_4 + residual_square_5
  -- END LITERAL GRAPH
  ⟨A, B, index_res, transport_res, auxiliary, strong, sum_5⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output = (graph p).A * (graph p).A + (graph p).B * (graph p).B + (graph p).index_res * (graph p).index_res + (graph p).transport_res * (graph p).transport_res + (graph p).auxiliary * (graph p).auxiliary + (graph p).strong * (graph p).strong := by
  rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the output is a common zero of the residuals. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 15 → V) :
    InternalZero (graph p).output v ↔ (graph p).A.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).B.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).index_res.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).transport_res.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).auxiliary.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).strong.evalRing (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff, output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  set x0 := (graph p).A.evalRing fun j => ι (v j)
  set x1 := (graph p).B.evalRing fun j => ι (v j)
  set x2 := (graph p).index_res.evalRing fun j => ι (v j)
  set x3 := (graph p).transport_res.evalRing fun j => ι (v j)
  set x4 := (graph p).auxiliary.evalRing fun j => ι (v j)
  set x5 := (graph p).strong.evalRing fun j => ι (v j)
  constructor
  · intro h
    have n0 := mul_self_nonneg x0
    have n1 := mul_self_nonneg x1
    have n2 := mul_self_nonneg x2
    have n3 := mul_self_nonneg x3
    have n4 := mul_self_nonneg x4
    have n5 := mul_self_nonneg x5
    exact ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    rw [h0, h1, h2, h3, h4, h5]
    ring

end Model

/-! ## Ring evaluation of the residuals -/

section Ring
variable {R : Type*} [CommRing R]

/-- The registers of this form. -/
def vv (p : Fin 4 → ℤ) (w : Fin 15 → R) : Vals R := vals p (3 * w 0 + 1) (fun _ => w 8) w

theorem A_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).A.evalRing w =
      ((vv p w).q3 * ((vv p w).ell + w 10) + w 9) * ((vv p w).q3 * ((vv p w).ell + w 10) + w 9) -
        ((vv p w).q3 * (vv p w).q3) * ((vv p w).ell * ((vv p w).ell + (vv p w).k) + 1) := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem B_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).B.evalRing w =
      ((vv p w).q * (vv p w).D0 + (vv p w).X * (vv p w).H) *
          ((vv p w).q * (vv p w).D0 + (vv p w).X * (vv p w).H) -
        (vv p w).q2 * ((vv p w).Delta * ((vv p w).c * (vv p w).c) + 1) := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem index_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).index_res.evalRing w = (((vv p w).k - w 5 * (vv p w).E) - 1) - (vv p w).RR := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem transport_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).transport_res.evalRing w =
      (vv p w).q * ((((p 1 : R) * (vv p w).C) - w 1) - w 3 * (vv p w).qm) + (vv p w).X * (vv p w).C := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem aux_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).auxiliary.evalRing w =
      rAux (vv p w).U (ordV (vv p w) (w 4) (w 7) (((vv p w).k - w 5 * (vv p w).E) - 1)) (w 13) := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem strong_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).strong.evalRing w =
      (w 6 * ((vv p w).c * (vv p w).c)) * (w 6 * ((vv p w).c * (vv p w).c)) - (vv p w).U := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P66p88Graph

#print axioms P66p88Graph.output_eq
#print axioms P66p88Graph.zero_iff
#print axioms P66p88Graph.A_eval
#print axioms P66p88Graph.B_eval
#print axioms P66p88Graph.index_eval
#print axioms P66p88Graph.transport_eval
#print axioms P66p88Graph.aux_eval
#print axioms P66p88Graph.strong_eval
