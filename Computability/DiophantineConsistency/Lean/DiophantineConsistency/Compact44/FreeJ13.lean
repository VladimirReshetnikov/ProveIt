import DiophantineConsistency.Compact44.FreeJSumSquares
import DiophantineConsistency.Compact44.FreeJSignedTransport
import Mathlib.Tactic.LinearCombination

/-! # The 13-positive, 87-operation free-J graph

Package 115's circuit `positive13_87_degree51.json` (13 positive inputs
`J F alpha f i T X Y r eta zeta u gamma`, the four compact ports, exact
degree 51). Gates 1–64 coincide with the 95-operation free-J literal's carrier
prefix. The tail replaces the ordinary residual `N` by two factors:

* `Fs = 1 + ((c²i)² − Q)`, the ordinary strong equation;
* `Fa = y² − Q(y² − V²)` with `y = V + u`, the auxiliary equation.

The output is `Fs·(Fa·((1+A0)(1+A1))) − 1`.

This module proves the ring-level facts. `embed x i u` is the 13-variable
valuation that reads the 12-variable valuation `x` with `f = 1 + t`. At
`embed x i u`, `A0` and `A1` evaluate to the 12-variable first and main
residuals at `x`, and the tail factors evaluate to explicit expressions in
the 12-variable `Q`, `V`. A ZMod 4 argument excludes the negative unit for
each of the four factors. The gate block between the markers is generated
from the JSON by `research/ordinary13-freej87-endpoint/generate_graph.py`,
which also checks it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace FreeJ13
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011

structure Graph where
  A0 : Expr (Fin 13)
  A1 : Expr (Fin 13)
  aux : Expr (Fin 13)
  strong : Expr (Fin 13)
  output : Expr (Fin 13)
  qm : Expr (Fin 13)
  z : Expr (Fin 13)
  n41 : Expr (Fin 13)
  u : Expr (Fin 13)
  a : Expr (Fin 13)
  c : Expr (Fin 13)
  d : Expr (Fin 13)
  y : Expr (Fin 13)
  vv : Expr (Fin 13)
  ii : Expr (Fin 13)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 13) := .var 0
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
  let g19 := a * c
  let b0 := X + g19
  let ell := E * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let folded_kBt := k * Bt
  let folded_g31 := g31 - folded_kBt
  let g32 := M * folded_g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let folded_q3Bt := q3 * Bt
  let Z := g34 - folded_q3Bt
  let g38 := Z * Z
  let g39 := M * M
  let g40 := ell * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
  let A0 := g38 - g42
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
  let rho := f2 - 1
  let Q := Delta * rho
  let I := c2 * i
  let g71 := I * I
  let g72 := g71 - Q
  let Fs := 1 + g72
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let F0 := 1 + A0
  let F1 := 1 + A1
  let g86 := F0 * F1
  let g87 := Fa * g86
  let g88 := Fs * g87
  let P13 := g88 - 1
  -- END LITERAL GRAPH
  ⟨A0, A1, Fa, Fs, P13, qm, Z, g41, U, a, c, Dstar, g78, V, I⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).strong * ((graph p).aux * ((1 + (graph p).A0) * (1 + (graph p).A1))) - 1 := by
  rfl

/-! ## Factor patterns and the negative-unit exclusions -/

def firstPattern {σ : Type*} (qm z n : Expr σ) : Expr σ :=
  let q := 1 + qm
  let m := q * (q*q) * qm
  1+(z*z-m*m*n)

def mainPattern {σ : Type*} (u a c d : Expr σ) : Expr σ :=
  1+(d*d-u*u*(1+(3+4*a+a*a)*(c*c)))

def auxPattern {σ : Type*} (y z a f : Expr σ) : Expr σ :=
  let Q := ((3+4*a)+a*a)*(f*f-1)
  y*y-Q*(y*y-z*z)

def strongPattern {σ : Type*} (I a f : Expr σ) : Expr σ :=
  1+(I*I-((3+4*a)+a*a)*(f*f-1))

theorem first_pattern (p : Fin 4 → ℤ) :
    1 + (graph p).A0 = firstPattern (graph p).qm (graph p).z (graph p).n41 := by rfl
theorem main_pattern (p : Fin 4 → ℤ) :
    1 + (graph p).A1 = mainPattern (graph p).u (graph p).a (graph p).c (graph p).d := by rfl
theorem aux_pattern (p : Fin 4 → ℤ) :
    (graph p).aux = auxPattern (graph p).y (graph p).vv (graph p).a (.var 3) := by rfl
theorem strong_pattern (p : Fin 4 → ℤ) :
    (graph p).strong = strongPattern (graph p).ii (graph p).a (.var 3) := by rfl

private theorem aux_bad : ∀ y z a f : ZMod 4,
    y^2-((a^2+4*a+3)*(f^2-1))*(y^2-z^2) ≠ -1 := by decide
private theorem strong_bad : ∀ I a f : ZMod 4,
    1+I^2-(a^2+4*a+3)*(f^2-1) ≠ -1 := by decide

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_ne {σ : Type*} (qm z n : Expr σ) (v : σ → V) :
    (pairEval (firstPattern qm z n) v).1 + 1 ≠ (pairEval (firstPattern qm z n) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let qv := 1 + syntaxEval (fun i => residue (v i)) qm
  let zv := syntaxEval (fun i => residue (v i)) z
  let nv := syntaxEval (fun i => residue (v i)) n
  have he : syntaxEval (fun i => residue (v i)) (firstPattern qm z n) =
      1+zv^2-(qv^3*(qv-1))^2*nv := by
    simp only [firstPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one]
    dsimp only [qv,zv,nv]
    ring
  rw [he] at hn
  exact first_bad qv zv nv hn

theorem main_ne {σ : Type*} (u a c d : Expr σ) (v : σ → V) :
    (pairEval (mainPattern u a c d) v).1 + 1 ≠ (pairEval (mainPattern u a c d) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let uv := syntaxEval (fun i => residue (v i)) u
  let av := syntaxEval (fun i => residue (v i)) a
  let cv := syntaxEval (fun i => residue (v i)) c
  let dv := syntaxEval (fun i => residue (v i)) d
  have he : syntaxEval (fun i => residue (v i)) (mainPattern u a c d) =
      1+dv^2-uv^2*(1+(av^2+4*av+3)*cv^2) := by
    simp only [mainPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one,
      Nat.cast_ofNat]
    dsimp only [uv,av,cv,dv]
    ring
  rw [he] at hn
  exact main_bad uv av cv dv hn

theorem aux_ne {σ : Type*} (y z a f : Expr σ) (v : σ → V) :
    (pairEval (auxPattern y z a f) v).1 + 1 ≠ (pairEval (auxPattern y z a f) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let yv := syntaxEval (fun i => residue (v i)) y
  let zv := syntaxEval (fun i => residue (v i)) z
  let av := syntaxEval (fun i => residue (v i)) a
  let fv := syntaxEval (fun i => residue (v i)) f
  have he : syntaxEval (fun i => residue (v i)) (auxPattern y z a f) =
      yv^2-((av^2+4*av+3)*(fv^2-1))*(yv^2-zv^2) := by
    simp only [auxPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one,
      Nat.cast_ofNat]
    dsimp only [yv,zv,av,fv]
    ring
  rw [he] at hn
  exact aux_bad yv zv av fv hn

theorem strong_ne {σ : Type*} (I a f : Expr σ) (v : σ → V) :
    (pairEval (strongPattern I a f) v).1 + 1 ≠ (pairEval (strongPattern I a f) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  let Iv := syntaxEval (fun i => residue (v i)) I
  let av := syntaxEval (fun i => residue (v i)) a
  let fv := syntaxEval (fun i => residue (v i)) f
  have he : syntaxEval (fun i => residue (v i)) (strongPattern I a f) =
      1+Iv^2-(av^2+4*av+3)*(fv^2-1) := by
    simp only [strongPattern, syntax_add, syntax_sub, syntax_mul, syntax_ofNat, Nat.cast_one,
      Nat.cast_ofNat]
    dsimp only [Iv,av,fv]
    ring
  rw [he] at hn
  exact strong_bad Iv av fv hn

/-! ## Four positive units -/

private theorem pairEval_mul13 (e f : Expr (Fin 13)) (v : Fin 13 → V) :
    pairEval (e*f) v = multiply (pairEval e v) (pairEval f v) := rfl

private theorem one_of_zero13 (e : Expr (Fin 13)) (v : Fin 13 → V)
    (hz : InternalZero (e-1) v) : Equivalent (pairEval e v) (natural (1:V)) := by
  apply equivalent_one.mpr
  change (Expr.sub e (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub e (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural,NatExpr.evalSemiring,pairEval] using hz

/-- A zero of the 87-operation graph makes each of its four factors the
positive unit. -/
theorem factor_units (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (graph p).output v) :
    (pairEval (1 + (graph p).A0) v).1 = (pairEval (1 + (graph p).A0) v).2 + 1 ∧
    (pairEval (1 + (graph p).A1) v).1 = (pairEval (1 + (graph p).A1) v).2 + 1 ∧
    (pairEval (graph p).aux v).1 = (pairEval (graph p).aux v).2 + 1 ∧
    (pairEval (graph p).strong v).1 = (pairEval (graph p).strong v).2 + 1 := by
  let a := pairEval (1 + (graph p).A0) v
  let b := pairEval (1 + (graph p).A1) v
  let c := pairEval (graph p).aux v
  let d := pairEval (graph p).strong v
  rw [output_eq] at hz
  have h := one_of_zero13 _ v hz
  rw [pairEval_mul13, pairEval_mul13, pairEval_mul13] at h
  have hs : Equivalent (product5 a b c d (natural (1:V))) (natural (1:V)) := by
    have he : product5 a b c d (natural (1:V)) =
        multiply d (multiply c (multiply a b)) := by
      unfold product5
      rw [multiply_one]
      apply Prod.ext <;> simp only [multiply] <;> ring
    rw [he]
    exact h
  obtain ⟨ha,hb,hc,hd,_⟩ := product5_magnitudes hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply equivalent_one.mp (positive_of_magnitude_one ha _)
    show (pairEval (1 + (graph p).A0) v).1 + 1 ≠ (pairEval (1 + (graph p).A0) v).2
    rw [first_pattern]; exact first_ne _ _ _ v
  · apply equivalent_one.mp (positive_of_magnitude_one hb _)
    show (pairEval (1 + (graph p).A1) v).1 + 1 ≠ (pairEval (1 + (graph p).A1) v).2
    rw [main_pattern]; exact main_ne _ _ _ _ v
  · apply equivalent_one.mp (positive_of_magnitude_one hc _)
    show (pairEval (graph p).aux v).1 + 1 ≠ (pairEval (graph p).aux v).2
    rw [aux_pattern]; exact aux_ne _ _ _ _ v
  · apply equivalent_one.mp (positive_of_magnitude_one hd _)
    show (pairEval (graph p).strong v).1 + 1 ≠ (pairEval (graph p).strong v).2
    rw [strong_pattern]; exact strong_ne _ _ _ v

/-- A pair is the positive unit iff the ring evaluation is one. -/
theorem unit_iff_one {σ : Type*} (e : Expr σ) (v : σ → V) :
    (pairEval e v).1 = (pairEval e v).2 + 1 ↔ e.evalRing (fun j => ι (v j)) = 1 := by
  rw [← split_evalRing, ← evalSemiring_map ι, ← evalSemiring_map ι, sub_eq_iff_eq_add,
    ← map_one ι, ← map_add, ι_injective.eq_iff, add_comm 1]
  rfl

/-! ## Evaluation at the embedded 12-variable valuation -/

section Ring
variable {R : Type*} [CommRing R]

/-- Read a 12-variable valuation (`J F alpha t T X Y r eta zeta n gamma`) as a
13-variable one (`J F alpha f i T X Y r eta zeta u gamma`) with `f = 1 + t`. -/
def embed (x : Fin 12 → R) (i u : R) : Fin 13 → R :=
  ![x 0, x 1, x 2, 1 + x 3, i, x 4, x 5, x 6, x 7, x 8, x 9, u, x 11]

@[simp] theorem embed_0 (x : Fin 12 → R) (i u : R) : embed x i u 0 = x 0 := rfl
@[simp] theorem embed_1 (x : Fin 12 → R) (i u : R) : embed x i u 1 = x 1 := rfl
@[simp] theorem embed_2 (x : Fin 12 → R) (i u : R) : embed x i u 2 = x 2 := rfl
@[simp] theorem embed_3 (x : Fin 12 → R) (i u : R) : embed x i u 3 = 1 + x 3 := rfl
@[simp] theorem embed_4 (x : Fin 12 → R) (i u : R) : embed x i u 4 = i := rfl
@[simp] theorem embed_5 (x : Fin 12 → R) (i u : R) : embed x i u 5 = x 4 := rfl
@[simp] theorem embed_6 (x : Fin 12 → R) (i u : R) : embed x i u 6 = x 5 := rfl
@[simp] theorem embed_7 (x : Fin 12 → R) (i u : R) : embed x i u 7 = x 6 := rfl
@[simp] theorem embed_8 (x : Fin 12 → R) (i u : R) : embed x i u 8 = x 7 := rfl
@[simp] theorem embed_9 (x : Fin 12 → R) (i u : R) : embed x i u 9 = x 8 := rfl
@[simp] theorem embed_10 (x : Fin 12 → R) (i u : R) : embed x i u 10 = x 9 := rfl
@[simp] theorem embed_11 (x : Fin 12 → R) (i u : R) : embed x i u 11 = u := rfl
@[simp] theorem embed_12 (x : Fin 12 → R) (i u : R) : embed x i u 12 = x 11 := rfl

theorem first_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) (i u : R) :
    (graph p).A0.evalRing (embed x i u) = (FreeJSumSquares.firstResidual p).evalRing x := by
  simp only [FreeJSumSquares.firstResidual, FreeJSumSquares.rightAdd,
    Ordinary12FreeJ.core, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    embed_0, embed_1, embed_2, embed_3, embed_4, embed_5, embed_6, embed_7, embed_8,
    embed_9, embed_10, embed_11, embed_12]

theorem main_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) (i u : R) :
    (graph p).A1.evalRing (embed x i u) = (FreeJSumSquares.mainResidual p).evalRing x := by
  simp only [FreeJSumSquares.mainResidual, FreeJSumSquares.rightAdd,
    Ordinary12FreeJ.core, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    embed_0, embed_1, embed_2, embed_3, embed_4, embed_5, embed_6, embed_7, embed_8,
    embed_9, embed_10, embed_11, embed_12]

open FreeJOrdinaryTransport in
theorem aux_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) (i u : R) :
    (graph p).aux.evalRing (embed x i u) =
      ((parts p).z.evalRing x + u) * ((parts p).z.evalRing x + u) -
        (parts p).q.evalRing x * (((parts p).z.evalRing x + u) * ((parts p).z.evalRing x + u) -
          (parts p).z.evalRing x * (parts p).z.evalRing x) := by
  simp only [parts, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    embed_0, embed_1, embed_2, embed_3, embed_4, embed_5, embed_6, embed_7, embed_8,
    embed_9, embed_10, embed_11, embed_12]

open FreeJOrdinaryTransport in
theorem strong_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) (i u : R) :
    (graph p).strong.evalRing (embed x i u) =
      1 + (((x 8 + x 6 * (x 8 + x 9)) * (x 8 + x 6 * (x 8 + x 9)) * i) *
        ((x 8 + x 6 * (x 8 + x 9)) * (x 8 + x 6 * (x 8 + x 9)) * i) - (parts p).q.evalRing x) := by
  simp only [parts, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    embed_0, embed_1, embed_2, embed_3, embed_4, embed_5, embed_6, embed_7, embed_8,
    embed_9, embed_10, embed_11, embed_12]

open FreeJOrdinaryTransport in
/-- The 12-variable ordinary residual `N` in terms of `Q`, `d`, `V`, `n`. -/
theorem ordinary_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) :
    (FreeJSumSquares.ordinaryResidual p).evalRing x =
      let Q := (parts p).q.evalRing x
      let d := (parts p).d.evalRing x
      let z := (parts p).z.evalRing x
      let n := (parts p).n.evalRing x
      (d*((1-Q)*((z+n)*(z+n)) + (Q*(z*z)-1)) - Q*(1-Q)) *
          (d*((1-Q)*((z+n)*(z+n)) + (Q*(z*z)-1)) - Q*(1-Q)) +
        (4*(d*(Q*(1-Q))))*(Q*(z*z)-1) := by
  simp only [FreeJSumSquares.ordinaryResidual, FreeJSumSquares.rightAdd,
    Ordinary12FreeJ.core, parts, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

open FreeJOrdinaryTransport in
theorem q_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) :
    (parts p).q.evalRing x =
      ((3 + 4*(x 5 * x 6 + x 6)) + (x 5 * x 6 + x 6) * (x 5 * x 6 + x 6)) *
        ((1 + x 3) * (1 + x 3) - 1) := by
  simp only [parts, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

open FreeJOrdinaryTransport in
theorem d_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) :
    (parts p).d.evalRing x =
      ((x 8 + x 6 * (x 8 + x 9)) * (x 8 + x 6 * (x 8 + x 9))) *
        ((x 8 + x 6 * (x 8 + x 9)) * (x 8 + x 6 * (x 8 + x 9))) := by
  simp only [parts, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

open FreeJOrdinaryTransport in
theorem n_eval (p : Fin 4 → ℤ) (x : Fin 12 → R) : (parts p).n.evalRing x = x 10 := by
  simp only [parts, Expr.evalRing_var]

/-! ## The two tail identities -/

/-- 13 → 12: the strong and auxiliary equations, with `n = i + u`, make the
12-variable ordinary residual vanish identically. -/
theorem tail_forward (Q d z i u : R) (hQ : Q = d*(i*i))
    (hA : (z+u)*(z+u) - Q*((z+u)*(z+u) - z*z) = 1) :
    (d*((1-Q)*((z+(i+u))*(z+(i+u))) + (Q*(z*z)-1)) - Q*(1-Q)) *
        (d*((1-Q)*((z+(i+u))*(z+(i+u))) + (Q*(z*z)-1)) - Q*(1-Q)) +
      (4*(d*(Q*(1-Q))))*(Q*(z*z)-1) = 0 := by
  subst hQ
  linear_combination
    (2*(2*d*(1-d*(i*i))*(z+u)*i)*d +
      d*d*((z+u)*(z+u) - d*(i*i)*((z+u)*(z+u) - z*z) - 1) +
      4*d*(d*(i*i))*(1-d*(i*i))) * hA

/-- 12 → 13: the 12-variable auxiliary equation `Q·V² = (Q−1)·y² + 1` makes
the 13-variable auxiliary factor one at `u = y − V`. -/
theorem tail_backward (Q z y : R) (h : Q*(z*z) = (Q-1)*(y*y)+1) :
    (z+(y-z))*(z+(y-z)) - Q*((z+(y-z))*(z+(y-z)) - z*z) = 1 := by
  linear_combination h

end Ring

end FreeJ13

#print axioms FreeJ13.output_eq
#print axioms FreeJ13.factor_units
#print axioms FreeJ13.unit_iff_one
#print axioms FreeJ13.first_eval
#print axioms FreeJ13.main_eval
#print axioms FreeJ13.aux_eval
#print axioms FreeJ13.strong_eval
#print axioms FreeJ13.ordinary_eval
#print axioms FreeJ13.q_eval
#print axioms FreeJ13.d_eval
#print axioms FreeJ13.tail_forward
#print axioms FreeJ13.tail_backward
