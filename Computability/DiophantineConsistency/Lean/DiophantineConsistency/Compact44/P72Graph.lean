import DiophantineConsistency.Compact44.FreeJSumSquares
import Mathlib.Tactic.LinearCombination

/-! # Package 72's 13-positive, 98-operation equation P13

`72-congruence-sextic/positive13/p13_degree28.json`: thirteen positive inputs
`F α C f0 i T X Y r η ζ u γ`, the four compact44 ports, and six derived fixed
leaves `B = β+1`, `b = 3β`, `b² `, `L = β·b²`, `Kfinal = b²L²`, `4β`. These are
constants computed from `p 0`, so they cost no operations. The output is
`A0² + A1² + Aa² + As²`.

The gate block is generated from the pinned JSON by
`research/ordinary13-p72-endpoint/tools/generate_p72.py`, which also checks it.
This module also proves the four-squares split of zeros and, for every
residual, its evaluation in an arbitrary commutative ring as an explicit
formula. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P72Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  Z : Expr (Fin 13)
  A0 : Expr (Fin 13)
  A1 : Expr (Fin 13)
  Aa : Expr (Fin 13)
  As : Expr (Fin 13)
  output : Expr (Fin 13)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let F : Expr (Fin 13) := .var 0
  let alpha : Expr (Fin 13) := .var 1
  let C : Expr (Fin 13) := .var 2
  let f0 : Expr (Fin 13) := .var 3
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
  let B : Expr (Fin 13) := .constant ((p 0) + 1)
  let b : Expr (Fin 13) := .constant (3 * (p 0))
  let b2 : Expr (Fin 13) := .constant ((3 * (p 0)) * (3 * (p 0)))
  let L : Expr (Fin 13) := .constant ((p 0) * ((3 * (p 0)) * (3 * (p 0))))
  let Kfinal : Expr (Fin 13) := .constant (((3 * (p 0)) * (3 * (p 0))) * (((p 0) * ((3 * (p 0)) * (3 * (p 0)))) * ((p 0) * ((3 * (p 0)) * (3 * (p 0))))))
  let four_beta : Expr (Fin 13) := .constant (4 * (p 0))
  let qF := C + alpha
  let q := F + qF
  let qm := q - 1
  let q2 := q * q
  let q3 := q * q2
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let E := X * Y
  let a := E + Y
  let g11 := 4 * a
  let H := 3 + g11
  let g13 := a * a
  let Delta := H + g13
  let ell := E * kY
  let ac := a * c
  let b0 := X + ac
  let g18 := b * f0
  let g19 := q - B
  let nF := g18 + g19
  let f2 := nF * nF
  let f2m := f2 - b2
  let I := c2 * i
  let g24 := I * I
  let g25 := Delta * g24
  let g26 := b2 * g25
  let As := f2m - g26
  let g28 := qF * qm
  let G := alpha + g28
  let g30 := q2 - 1
  let g31 := G * g30
  let g32 := beta * g31
  let g33 := MF * q
  let g34 := MC + g33
  let g35 := g34 * qm
  let Rhat := g32 + g35
  let M0 := q3 * qm
  let g38 := K0 * q
  let g39 := X + g38
  let g40 := C * g39
  let g41 := F * q
  let Bt := g40 - g41
  let g43 := ell + r
  let g44 := M0 * g43
  let g45 := Y * qm
  let g46 := g44 + g45
  let g47 := Bt * q3
  let Z := g46 - g47
  let g49 := ell + k
  let g50 := ell * g49
  let rad0 := 1 + g50
  let g52 := Z * Z
  let g53 := M0 * M0
  let g54 := g53 * rad0
  let A0 := g52 - g54
  let g56 := Y * q
  let Sb := four_beta * g56
  let Mb := Sb * q
  let g59 := Mb * gamma
  let g60 := Sb * X
  let g61 := g59 + g60
  let g62 := k - 1
  let g63 := beta * g62
  let g64 := g61 - g63
  let shift := Rhat + g64
  let g66 := Mb * b0
  let g67 := H * shift
  let Dhat := g66 + g67
  let g69 := Dhat * Dhat
  let g70 := Mb * Mb
  let g71 := Delta * c2
  let g72 := 1 + g71
  let g73 := g70 * g72
  let A1 := g69 - g73
  let g75 := beta * c
  let g76 := T * g75
  let g77 := g76 - Rhat
  let g78 := f2 * g77
  let g79 := L * c
  let Vhat := g78 - g79
  let g81 := L * u
  let yhat := Vhat + g81
  let yhat2 := yhat * yhat
  let g84 := b2 * yhat2
  let g85 := Delta * f2m
  let g86 := Vhat * Vhat
  let g87 := yhat2 - g86
  let g88 := g85 * g87
  let g89 := g84 - g88
  let Aa := g89 - Kfinal
  let g91 := A0 * A0
  let g92 := A1 * A1
  let g93 := g91 + g92
  let g94 := Aa * Aa
  let g95 := g93 + g94
  let g96 := As * As
  let g97 := g95 + g96
  -- END LITERAL GRAPH
  ⟨Z, A0, A1, Aa, As, g97⟩

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
    have ha0 : a * a = 0 := by linarith
    have hb0 : b * b = 0 := by linarith
    have hc0 : c * c = 0 := by linarith
    have hd0 : d * d = 0 := by linarith
    exact ⟨mul_self_eq_zero.mp ha0, mul_self_eq_zero.mp hb0, mul_self_eq_zero.mp hc0,
      mul_self_eq_zero.mp hd0⟩
  · rintro ⟨ha, hb, hc, hd⟩
    rw [ha, hb, hc, hd]
    ring

/-! ## Ring evaluation of the residuals -/

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values, gate by gate. -/
structure Vals (R : Type*) where
  q : R
  k : R
  c : R
  a : R
  H : R
  Delta : R
  ell : R
  Nf : R
  I : R
  Rhat : R
  M0 : R
  Bt : R
  Z : R
  Sb : R
  Mb : R
  Dhat : R
  Vhat : R
  yhat : R

def vals (p : Fin 4 → ℤ) (w : Fin 13 → R) : Vals R :=
  let beta : R := (p 0 : R)
  let q := w 0 + (w 2 + w 1)
  let qm := q - 1
  let k := w 9 + w 10
  let kY := w 7 * k
  let c := w 9 + kY
  let E := w 6 * w 7
  let a := E + w 7
  let H := 3 + 4 * a
  let Delta := H + a * a
  let ell := E * kY
  let Nf := (3 * beta) * w 3 + (q - (beta + 1))
  let I := (c * c) * w 4
  let G := w 1 + (w 2 + w 1) * qm
  let Rhat := beta * (G * (q * q - 1)) + ((p 2 : R) + (p 3 : R) * q) * qm
  let M0 := (q * (q * q)) * qm
  let Bt := w 2 * (w 6 + (p 1 : R) * q) - w 0 * q
  let Z := (M0 * (ell + w 8) + w 7 * qm) - Bt * (q * (q * q))
  let Sb := (4 * beta) * (w 7 * q)
  let Mb := Sb * q
  let Dhat := Mb * (w 6 + a * c) +
    H * (Rhat + ((Mb * w 12 + Sb * w 6) - beta * (k - 1)))
  let L := beta * ((3 * beta) * (3 * beta))
  let Vhat := (Nf * Nf) * (w 5 * (beta * c) - Rhat) - L * c
  let yhat := Vhat + L * w 11
  ⟨q, k, c, a, H, Delta, ell, Nf, I, Rhat, M0, Bt, Z, Sb, Mb, Dhat, Vhat, yhat⟩

theorem Z_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).Z.evalRing w = (vals p w).Z := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem A0_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).A0.evalRing w =
      (vals p w).Z * (vals p w).Z - ((vals p w).M0 * (vals p w).M0) *
        (1 + (vals p w).ell * ((vals p w).ell + (vals p w).k)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem A1_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).A1.evalRing w =
      (vals p w).Dhat * (vals p w).Dhat - ((vals p w).Mb * (vals p w).Mb) *
        (1 + (vals p w).Delta * ((vals p w).c * (vals p w).c)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat, Int.cast_add, Int.cast_mul]

theorem As_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).As.evalRing w =
      ((vals p w).Nf * (vals p w).Nf - (3 * (p 0 : R)) * (3 * (p 0 : R))) -
        ((3 * (p 0 : R)) * (3 * (p 0 : R))) * ((vals p w).Delta * ((vals p w).I * (vals p w).I)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat, Int.cast_add, Int.cast_mul]

theorem Aa_eval (p : Fin 4 → ℤ) (w : Fin 13 → R) :
    (graph p).Aa.evalRing w =
      ((3 * (p 0 : R)) * (3 * (p 0 : R)) * ((vals p w).yhat * (vals p w).yhat) -
        ((vals p w).Delta * ((vals p w).Nf * (vals p w).Nf - (3 * (p 0 : R)) * (3 * (p 0 : R)))) *
          ((vals p w).yhat * (vals p w).yhat - (vals p w).Vhat * (vals p w).Vhat)) -
      ((3 * (p 0 : R)) * (3 * (p 0 : R))) *
        (((p 0 : R) * ((3 * (p 0 : R)) * (3 * (p 0 : R)))) *
          ((p 0 : R) * ((3 * (p 0 : R)) * (3 * (p 0 : R))))) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat, Int.cast_add, Int.cast_mul]

end Ring

end P72Graph

#print axioms P72Graph.output_eq
#print axioms P72Graph.zero_iff
#print axioms P72Graph.Z_eval
#print axioms P72Graph.A0_eval
#print axioms P72Graph.A1_eval
#print axioms P72Graph.As_eval
#print axioms P72Graph.Aa_eval
