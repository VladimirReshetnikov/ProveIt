import DiophantineConsistency.Compact44.P66Vals

/-! # Package 66's 15-positive, 78-operation equation of degree 30

`66-gap-congruence/algebra/p15_78_degree30.json`: fifteen positive inputs
`J F α z f h i T w Y r η ζ u γ` and the four compact44 ports `β K0 MC MF`; 78
operations, exact degree 30 (package 58's 79-operation `p15_degree30.json` with
`2V + u` computed as `V + (V + u)`). With `q = βJ + 1`, `X = wq` and `Y` free, the
output is `A² + paired² + auxiliary² + strong²`, where (`P66Vals`)

* `A = (q³(ℓ + r) + Y)² − q⁶(ℓ(ℓ + k) + 1)`, the integral-root first carrier;
* `paired = N1·Nk·Nt − 1` with `N1 = D0² − Δc²`, `D0 = ac + (X + γH)`,
  `Nk = (k − hE) − R` and `Nt = ((K0 + w)C + (q − F)) − z(q − 1)`;
* `auxiliary = (V + u)² − U·u(V + (V + u)) − 1` with `U = Δ(f² − 1)` and
  `V = f²(cT − R) − c`;
* `strong = (ic²)² − U`.

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
namespace P66p78Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing P66Vals

structure Graph where
  A : Expr (Fin 15)
  paired : Expr (Fin 15)
  auxiliary : Expr (Fin 15)
  strong : Expr (Fin 15)
  output : Expr (Fin 15)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 15) := .var 0
  let F : Expr (Fin 15) := .var 1
  let alpha : Expr (Fin 15) := .var 2
  let z : Expr (Fin 15) := .var 3
  let f : Expr (Fin 15) := .var 4
  let h : Expr (Fin 15) := .var 5
  let i : Expr (Fin 15) := .var 6
  let T : Expr (Fin 15) := .var 7
  let w : Expr (Fin 15) := .var 8
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
  let qm := beta * J
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let q6 := q3 * q3
  let qF := q - F
  let C := qF - alpha
  let Xvalue := w * q
  let E := Xvalue * Y
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
  let Z := Xvalue + gammaH
  let D0 := ac + Z
  let ell := E * kY
  let ell_r := ell + r
  let g24 := q3 * ell_r
  let first_num := g24 + Y
  let g26 := ell + k
  let g27 := ell * g26
  let first_rhs := g27 + 1
  let g29 := first_num * first_num
  let g30 := q6 * first_rhs
  let A := g29 - g30
  let g32 := D0 * D0
  let g33 := Delta * c2
  let N1 := g32 - g33
  let g35 := qm * qF
  let g36 := g35 + alpha
  let g37 := q2 - 1
  let g38 := g36 * g37
  let g39 := q * MF
  let g40 := MC + g39
  let g41 := g40 * J
  let R := g38 + g41
  let g43 := h * E
  let kmhE := k - g43
  let Nk := kmhE - R
  let g46 := K0 + w
  let g47 := g46 * C
  let g48 := g47 + qF
  let g49 := z * qm
  let Nt := g48 - g49
  let g51 := N1 * Nk
  let g52 := g51 * Nt
  let paired := g52 - 1
  let f2 := f * f
  let g55 := f2 - 1
  let U := Delta * g55
  let I := i * c2
  let g58 := I * I
  let strong := g58 - U
  let g60 := c * T
  let g61 := g60 - R
  let g62 := f2 * g61
  let V := g62 - c
  let vu := V + u
  let g65 := vu * vu
  let g67 := V + vu
  let g68 := u * g67
  let g69 := U * g68
  let g70 := g65 - g69
  let auxiliary := g70 - 1
  let residual_square_0 := A * A
  let residual_square_1 := paired * paired
  let residual_square_2 := auxiliary * auxiliary
  let residual_square_3 := strong * strong
  let sum_1 := residual_square_0 + residual_square_1
  let sum_2 := sum_1 + residual_square_2
  let sum_3 := sum_2 + residual_square_3
  -- END LITERAL GRAPH
  ⟨A, paired, auxiliary, strong, sum_3⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output = (graph p).A * (graph p).A + (graph p).paired * (graph p).paired + (graph p).auxiliary * (graph p).auxiliary + (graph p).strong * (graph p).strong := by
  rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the output is a common zero of the residuals. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 15 → V) :
    InternalZero (graph p).output v ↔ (graph p).A.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).paired.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).auxiliary.evalRing (fun j => ι (v j)) = 0 ∧ (graph p).strong.evalRing (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff, output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  set x0 := (graph p).A.evalRing fun j => ι (v j)
  set x1 := (graph p).paired.evalRing fun j => ι (v j)
  set x2 := (graph p).auxiliary.evalRing fun j => ι (v j)
  set x3 := (graph p).strong.evalRing fun j => ι (v j)
  constructor
  · intro h
    have n0 := mul_self_nonneg x0
    have n1 := mul_self_nonneg x1
    have n2 := mul_self_nonneg x2
    have n3 := mul_self_nonneg x3
    exact ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith)⟩
  · rintro ⟨h0, h1, h2, h3⟩
    rw [h0, h1, h2, h3]
    ring

end Model

/-! ## Ring evaluation of the residuals -/

section Ring
variable {R : Type*} [CommRing R]

/-- The registers of this form. -/
def vv (p : Fin 4 → ℤ) (w : Fin 15 → R) : Vals R := vals p (w 0) (fun q => w 8 * q) w

theorem A_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).A.evalRing w =
      ((vv p w).q3 * ((vv p w).ell + w 10) + w 9) * ((vv p w).q3 * ((vv p w).ell + w 10) + w 9) -
        ((vv p w).q3 * (vv p w).q3) * ((vv p w).ell * ((vv p w).ell + (vv p w).k) + 1) := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem paired_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).paired.evalRing w =
      ((vv p w).D0 * (vv p w).D0 - (vv p w).Delta * ((vv p w).c * (vv p w).c)) *
          (((vv p w).k - w 5 * (vv p w).E) - (vv p w).RR) *
          ((((p 1 : R) + w 8) * (vv p w).C + (vv p w).qF) - w 3 * (vv p w).qm) - 1 := by
  simp only [graph, vv, vals, rAux, ordV, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem aux_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).auxiliary.evalRing w =
      rAux (vv p w).U (ordV (vv p w) (w 4) (w 7) (vv p w).RR) (w 13) := by
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

end P66p78Graph

#print axioms P66p78Graph.output_eq
#print axioms P66p78Graph.zero_iff
#print axioms P66p78Graph.A_eval
#print axioms P66p78Graph.paired_eval
#print axioms P66p78Graph.aux_eval
#print axioms P66p78Graph.strong_eval
