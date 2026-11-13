import DiophantineConsistency.Compact44.FreeJ13
import Mathlib.Tactic.LinearCombination

/-! # Package 73's 13-positive, 92-operation equation of degree 30

`73-guard-reanchoring/positive/p13_degree30.json`: thirteen positive inputs
`j F α f i T X Y r η ζ u γ` and the four compact44 ports. With `J = 3j + 1`
and `q = 1 + Jβ`, its four residuals are:

* `A0`, the free-J literal's first carrier. Its `W = 1 + k(q−1)` unfolds the
  literal's folded `k·Bt`;
* `A1`, the free-J literal's main carrier, with modulus `U = q²Y`;
* `As = f² − 1 − Δ(c²i)²`, the normalized strong norm;
* `Aa = (V+u)² − Δ(f²−1)((V+u)² − V²) − 1`, the auxiliary norm.

The output is `A0² + A1² + Aa² + As²`. The gate block is generated from the
pinned JSON by `research/thirteen-p73-endpoint/tools/generate_p73.py`, which
also checks it.

`lift w` is the 12-variable free-J valuation
`![3j+1, F, α, f−1, T, X, Y, r, η, ζ, Δi + u, γ]`. At `lift w`, the literal's
first and main residuals are `A0` and `A1`, and its tail registers are
`Q = Δ(f²−1)`, `c⁴`, `V` and `Δi + u`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P73Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  A0 : Expr (Fin 13)
  A1 : Expr (Fin 13)
  Aa : Expr (Fin 13)
  As : Expr (Fin 13)
  output : Expr (Fin 13)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let j : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let X : Expr (Fin 13) := .var 6
  let Y : Expr (Fin 13) := .var 7
  let r : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let u : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let beta : Expr (Fin 13) := .constant (p 0)
  let K0 : Expr (Fin 13) := .constant (p 1)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let g0 := 3 * j
  let J := 1 + g0
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let a := E + Y
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let ac := a * c
  let b0 := X + ac
  let ell := E * kY
  let g22 := k * qm
  let W := 1 + g22
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let g32 := M * g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let g35 := W * q3
  let g36 := Bt * g35
  let root0 := g34 - g36
  let g38 := ell * g30
  let rad0 := 1 + g38
  let g40 := root0 * root0
  let g41 := M * M
  let g42 := g41 * rad0
  let A0 := g40 - g42
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - R
  let r0 := g52 - 1
  let g54 := U * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := U * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := U * U
  let g63 := Delta * c2
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f2 := f * f
  let f2m := f2 - 1
  let Kaux := Delta * f2m
  let I := c2 * i
  let g71 := I * I
  let g72 := Delta * g71
  let As := f2m - g72
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Kaux * g81
  let g83 := y2 - g82
  let Aa := g83 - 1
  let g85 := A0 * A0
  let g86 := A1 * A1
  let g87 := g85 + g86
  let g88 := Aa * Aa
  let g89 := g87 + g88
  let g90 := As * As
  let g91 := g89 + g90
  -- END LITERAL GRAPH
  ⟨A0, A1, Aa, As, g91⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).A0 * (graph p).A0 + (graph p).A1 * (graph p).A1 +
      (graph p).Aa * (graph p).Aa + (graph p).As * (graph p).As := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the output is a common zero of the four residuals. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (graph p).output v ↔
      InternalZero (graph p).A0 v ∧ InternalZero (graph p).A1 v ∧
        InternalZero (graph p).Aa v ∧ InternalZero (graph p).As v := by
  rw [output_eq, internalZero_iff, internalZero_iff, internalZero_iff, internalZero_iff,
    internalZero_iff]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  set a := (graph p).A0.evalRing fun j => ι (v j)
  set b := (graph p).A1.evalRing fun j => ι (v j)
  set c := (graph p).Aa.evalRing fun j => ι (v j)
  set d := (graph p).As.evalRing fun j => ι (v j)
  constructor
  · intro h
    have ha := mul_self_nonneg a
    have hb := mul_self_nonneg b
    have hc := mul_self_nonneg c
    have hd := mul_self_nonneg d
    exact ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith),
      mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith)⟩
  · rintro ⟨ha, hb, hc, hd⟩
    rw [ha, hb, hc, hd]
    ring

/-! ## Ring evaluation of the residuals -/

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values, gate by gate. -/
structure Vals (R : Type*) where
  J : R
  qm : R
  q : R
  q3 : R
  U : R
  C : R
  E : R
  k : R
  c : R
  a : R
  H : R
  Delta : R
  ell : R
  M : R
  Bt : R
  root0 : R
  RR : R
  Dstar : R
  Kaux : R
  V : R

def vals (p : Fin 4 → ℤ) (w : Fin 13 → R) : Vals R :=
  let J := 1 + 3 * w 0
  let qm := J * (p 0 : R)
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := w 7 * q2
  let qF := q - w 1
  let C := qF - w 2
  let E := w 6 * w 7
  let k := w 9 + w 10
  let kY := w 7 * k
  let c := w 9 + kY
  let a := E + w 7
  let H := 3 + 4 * a
  let Delta := H + a * a
  let ell := E * kY
  let W := 1 + k * qm
  let M := q3 * qm
  let Bt := C * (w 6 + (p 1 : R) * q) - w 1 * q
  let root0 := (M * ((ell + k) + w 8) + w 7 * qm) - Bt * (W * q3)
  let G := w 2 + qF * qm
  let RR := G * (q2 - 1) + J * ((p 2 : R) + (p 3 : R) * q)
  let shift := (U * w 12 + E * q) - ((k - RR) - 1)
  let Dstar := U * (w 6 + a * c) + H * shift
  let Kaux := Delta * (w 3 * w 3 - 1)
  let VV := (w 3 * w 3) * (w 5 * c - RR) - c
  ⟨J, qm, q, q3, U, C, E, k, c, a, H, Delta, ell, M, Bt, root0, RR, Dstar, Kaux, VV⟩

theorem A0_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).A0.evalRing w = (vals p w).root0 * (vals p w).root0 -
      ((vals p w).M * (vals p w).M) * (1 + (vals p w).ell * ((vals p w).ell + (vals p w).k)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem A1_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).A1.evalRing w = (vals p w).Dstar * (vals p w).Dstar -
      ((vals p w).U * (vals p w).U) * (1 + (vals p w).Delta * ((vals p w).c * (vals p w).c)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem As_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).As.evalRing w = (w 3 * w 3 - 1) - (vals p w).Delta *
      ((((vals p w).c * (vals p w).c) * w 4) * (((vals p w).c * (vals p w).c) * w 4)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Aa_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).Aa.evalRing w =
      ((((vals p w).V + w 11) * ((vals p w).V + w 11) -
        (vals p w).Kaux * (((vals p w).V + w 11) * ((vals p w).V + w 11) -
          (vals p w).V * (vals p w).V))) - 1 := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

/-! ## The free-J literal at `lift w` -/

/-- The 12-variable free-J valuation read off a 13-variable valuation. -/
def lift (p : Fin 4 → ℤ) (w : Fin 13 → R) : Fin 12 → R :=
  ![1 + 3 * w 0, w 1, w 2, w 3 - 1, w 5, w 6, w 7, w 8, w 9, w 10,
    (vals p w).Delta * w 4 + w 11, w 12]

section
variable (p : Fin 4 → ℤ) (w : Fin 13 → R)
@[simp] theorem lift_0 : lift p w 0 = 1 + 3 * w 0 := rfl
@[simp] theorem lift_1 : lift p w 1 = w 1 := rfl
@[simp] theorem lift_2 : lift p w 2 = w 2 := rfl
@[simp] theorem lift_3 : lift p w 3 = w 3 - 1 := rfl
@[simp] theorem lift_4 : lift p w 4 = w 5 := rfl
@[simp] theorem lift_5 : lift p w 5 = w 6 := rfl
@[simp] theorem lift_6 : lift p w 6 = w 7 := rfl
@[simp] theorem lift_7 : lift p w 7 = w 8 := rfl
@[simp] theorem lift_8 : lift p w 8 = w 9 := rfl
@[simp] theorem lift_9 : lift p w 9 = w 10 := rfl
@[simp] theorem lift_10 : lift p w 10 = (vals p w).Delta * w 4 + w 11 := rfl
@[simp] theorem lift_11 : lift p w 11 = w 12 := rfl
end

/-- The literal's first residual at `lift w`, in the register atoms of `vals`:
its `Z` folds `k·Bt` into the first factor. -/
theorem lit_first (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (FreeJSumSquares.firstResidual p).evalRing (lift p w) =
      ((vals p w).M * ((((vals p w).ell + (vals p w).k) + w 8) - (vals p w).k * (vals p w).Bt) +
          w 7 * (vals p w).qm - (vals p w).q3 * (vals p w).Bt) *
        ((vals p w).M * ((((vals p w).ell + (vals p w).k) + w 8) - (vals p w).k * (vals p w).Bt) +
          w 7 * (vals p w).qm - (vals p w).q3 * (vals p w).Bt) -
      ((vals p w).M * (vals p w).M) * (1 + (vals p w).ell * ((vals p w).ell + (vals p w).k)) := by
  simp only [FreeJSumSquares.firstResidual, FreeJSumSquares.rightAdd, Ordinary12FreeJ.core, vals,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one,
    Nat.cast_ofNat, lift_0, lift_1, lift_2, lift_3, lift_4, lift_5, lift_6, lift_7, lift_8,
    lift_9, lift_10, lift_11]

theorem first_lift (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (FreeJSumSquares.firstResidual p).evalRing (lift p w) = (graph p).A0.evalRing w := by
  rw [lit_first, A0_eval]
  have hroot : (vals p w).root0 = ((vals p w).M * (((vals p w).ell + (vals p w).k) + w 8) +
      w 7 * (vals p w).qm) - (vals p w).Bt * ((1 + (vals p w).k * (vals p w).qm) * (vals p w).q3) := rfl
  have hM : (vals p w).M = (vals p w).q3 * (vals p w).qm := rfl
  have hZ : (vals p w).M * ((((vals p w).ell + (vals p w).k) + w 8) - (vals p w).k * (vals p w).Bt) +
      w 7 * (vals p w).qm - (vals p w).q3 * (vals p w).Bt = (vals p w).root0 := by
    rw [hroot]; linear_combination (-((vals p w).Bt * (vals p w).k)) * hM
  rw [hZ]

theorem main_lift (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (FreeJSumSquares.mainResidual p).evalRing (lift p w) = (graph p).A1.evalRing w := by
  rw [A1_eval]
  simp only [FreeJSumSquares.mainResidual, FreeJSumSquares.rightAdd, Ordinary12FreeJ.core, vals,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one,
    Nat.cast_ofNat, lift_0, lift_1, lift_2, lift_3, lift_4, lift_5, lift_6, lift_7, lift_8,
    lift_9, lift_10, lift_11]

open FreeJOrdinaryTransport in
theorem q_lift (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (parts p).q.evalRing (lift p w) = (vals p w).Kaux := by
  rw [FreeJ13.q_eval]
  simp only [vals, lift_3, lift_5, lift_6]
  ring

open FreeJOrdinaryTransport in
theorem d_lift (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (parts p).d.evalRing (lift p w) = ((vals p w).c * (vals p w).c) * ((vals p w).c * (vals p w).c) := by
  rw [FreeJ13.d_eval]
  simp only [vals, lift_6, lift_8, lift_9]

open FreeJOrdinaryTransport in
theorem z_lift (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (parts p).z.evalRing (lift p w) = (vals p w).V := by
  simp only [parts, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat,
    Nat.cast_one, Nat.cast_ofNat, lift_0, lift_1, lift_2, lift_3, lift_4, lift_5, lift_6, lift_7,
    lift_8, lift_9, lift_10, lift_11]
  ring

open FreeJOrdinaryTransport in
theorem n_lift (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (parts p).n.evalRing (lift p w) = (vals p w).Delta * w 4 + w 11 := by
  rw [FreeJ13.n_eval, lift_10]

end Ring

end P73Graph

#print axioms P73Graph.zero_iff
#print axioms P73Graph.A0_eval
#print axioms P73Graph.A1_eval
#print axioms P73Graph.As_eval
#print axioms P73Graph.Aa_eval
#print axioms P73Graph.lit_first
#print axioms P73Graph.first_lift
#print axioms P73Graph.main_lift
#print axioms P73Graph.q_lift
#print axioms P73Graph.d_lift
#print axioms P73Graph.z_lift
#print axioms P73Graph.n_lift
