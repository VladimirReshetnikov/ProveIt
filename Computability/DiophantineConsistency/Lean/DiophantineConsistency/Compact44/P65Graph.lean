import DiophantineConsistency.Compact44.FreeJSumSquares
import Mathlib.Tactic.LinearCombination

/-! # Package 65's 14-positive, 92-operation equation of degree 26

`65-shared-taps/pell/circuits/p14_degree26.json`: fourteen positive inputs
`j F α z f i T x Y r η ζ u γ` and the four compact44 ports `β K0 MC MF`.
With `J = 3j+1`, `q = 1 + βJ`, `C = q − F − α` and `X = q + x`, its five
residuals are:

* `A0 = (Y + q³(r + ℓ))² − q⁶(1 + ℓ(ℓ+k))`, the first carrier;
* `Nm = D*² − M²(1 + Δc²)` with `D* = M(ca + X) + H(γM − (k − R − 1) + SX)`,
  `S = 4qY` and `M = qS`, the main carrier;
* `At = CX + q(K0·C − F − βJ·z)`, the transport;
* `Aa = (u+V)² − uU(u + 2V) − 1` with `U = Δ(f²−1)`, `V = f²(Tc − R) − c`,
  the auxiliary norm;
* `As = (i c²)² − U`, the ordinary strong norm.

The output is `As² + (Aa² + (At² + (A0² + Nm²)))`. The gate block is generated
from the pinned JSON by `research/fourteen-p65-endpoint/tools/generate_p65.py`,
which also checks it. This module proves the five-squares split of zeros and,
for every residual, its evaluation in an arbitrary commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P65Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  A0 : Expr (Fin 14)
  Nm : Expr (Fin 14)
  At : Expr (Fin 14)
  Aa : Expr (Fin 14)
  As : Expr (Fin 14)
  output : Expr (Fin 14)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let j : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let x : Expr (Fin 14) := .var 7
  let Y : Expr (Fin 14) := .var 8
  let r : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let u : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let v0 := 3 * j
  let v1 := 1 + v0
  let v2 := beta * v1
  let q := 1 + v2
  let v4 := q - F
  let v5 := v4 - alpha
  let v6 := q * q
  let X := q + x
  let E := Y * X
  let k := eta + zeta
  let v10 := Y * k
  let c := eta + v10
  let a := Y + E
  let v13 := 4 * a
  let H := 3 + v13
  let v15 := a * a
  let Delta := H + v15
  let ell := v10 * E
  let v18 := q * v6
  let v19 := v18 * v18
  let v20 := v2 * v4
  let v21 := alpha + v20
  let v22 := v6 - 1
  let v23 := v21 * v22
  let v24 := MF * q
  let v25 := MC + v24
  let v26 := v1 * v25
  let R := v23 + v26
  let v28 := Y * q
  let S := 4 * v28
  let M := S * q
  let v31 := k - R
  let v32 := v31 - 1
  let v33 := c * a
  let v34 := v33 + X
  let v35 := M * v34
  let v36 := gamma * M
  let v37 := v36 - v32
  let v38 := S * X
  let v39 := v37 + v38
  let v40 := H * v39
  let Dstar := v35 + v40
  let v42 := c * c
  let v43 := Dstar * Dstar
  let v44 := M * M
  let v45 := Delta * v42
  let v46 := 1 + v45
  let v47 := v44 * v46
  let Nm := v43 - v47
  let v49 := r + ell
  let v50 := v18 * v49
  let v51 := Y + v50
  let v52 := v51 * v51
  let v53 := ell + k
  let v54 := ell * v53
  let v55 := 1 + v54
  let v56 := v19 * v55
  let A0 := v52 - v56
  let v58 := f * f
  let v59 := v58 - 1
  let U := Delta * v59
  let v61 := i * v42
  let v62 := v61 * v61
  let As := v62 - U
  let v64 := T * c
  let v65 := v64 - R
  let v66 := v58 * v65
  let V := v66 - c
  let v68 := u + V
  let v69 := v68 * v68
  let v70 := u * U
  let v71 := V + V
  let v72 := u + v71
  let v73 := v70 * v72
  let v74 := v69 - v73
  let Aa := v74 - 1
  let v76 := K0 * v5
  let v77 := v2 * z
  let v78 := v5 * X
  let v79 := v76 - F
  let v80 := v79 - v77
  let v81 := q * v80
  let At := v78 + v81
  let v83 := A0 * A0
  let v84 := Nm * Nm
  let v85 := At * At
  let v86 := Aa * Aa
  let v87 := As * As
  let v88 := v83 + v84
  let v89 := v85 + v88
  let v90 := v86 + v89
  let v91 := v87 + v90
  let P26 := v91
  -- END LITERAL GRAPH
  ⟨A0, Nm, At, Aa, As, P26⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).As * (graph p).As + ((graph p).Aa * (graph p).Aa +
      ((graph p).At * (graph p).At + ((graph p).A0 * (graph p).A0 + (graph p).Nm * (graph p).Nm))) := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the output is a common zero of the five residuals. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (graph p).output v ↔
      InternalZero (graph p).A0 v ∧ InternalZero (graph p).Nm v ∧ InternalZero (graph p).At v ∧
        InternalZero (graph p).Aa v ∧ InternalZero (graph p).As v := by
  rw [output_eq, internalZero_iff, internalZero_iff, internalZero_iff, internalZero_iff,
    internalZero_iff, internalZero_iff]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  set a := (graph p).A0.evalRing fun j => ι (v j)
  set b := (graph p).Nm.evalRing fun j => ι (v j)
  set c := (graph p).At.evalRing fun j => ι (v j)
  set d := (graph p).Aa.evalRing fun j => ι (v j)
  set e := (graph p).As.evalRing fun j => ι (v j)
  constructor
  · intro h
    have ha := mul_self_nonneg a
    have hb := mul_self_nonneg b
    have hc := mul_self_nonneg c
    have hd := mul_self_nonneg d
    have he := mul_self_nonneg e
    exact ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith),
      mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith),
      mul_self_eq_zero.mp (by linarith)⟩
  · rintro ⟨ha, hb, hc, hd, he⟩
    rw [ha, hb, hc, hd, he]
    ring

/-! ## Ring evaluation of the residuals -/

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values, gate by gate. -/
structure Vals (R : Type*) where
  bJ : R
  q : R
  C : R
  X : R
  k : R
  c : R
  a : R
  H : R
  Delta : R
  ell : R
  q3 : R
  RR : R
  S : R
  M : R
  Dstar : R
  U : R
  V : R

def vals (p : Fin 4 → ℤ) (w : Fin 14 → R) : Vals R :=
  let beta : R := (p 0 : R)
  let bJ := beta * (1 + 3 * w 0)
  let q := 1 + bJ
  let C := (q - w 1) - w 2
  let X := q + w 7
  let E := w 8 * X
  let k := w 10 + w 11
  let kY := w 8 * k
  let c := w 10 + kY
  let a := w 8 + E
  let H := 3 + 4 * a
  let Delta := H + a * a
  let ell := kY * E
  let q3 := q * (q * q)
  let RR := (w 2 + bJ * (q - w 1)) * (q * q - 1) + (1 + 3 * w 0) * ((p 2 : R) + (p 3 : R) * q)
  let S := 4 * (w 8 * q)
  let M := S * q
  let Dstar := M * (c * a + X) + H * ((w 13 * M - ((k - RR) - 1)) + S * X)
  let U := Delta * (w 4 * w 4 - 1)
  let VV := (w 4 * w 4) * (w 6 * c - RR) - c
  ⟨bJ, q, C, X, k, c, a, H, Delta, ell, q3, RR, S, M, Dstar, U, VV⟩

theorem A0_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).A0.evalRing w =
      (w 8 + (vals p w).q3 * (w 9 + (vals p w).ell)) * (w 8 + (vals p w).q3 * (w 9 + (vals p w).ell)) -
        ((vals p w).q3 * (vals p w).q3) * (1 + (vals p w).ell * ((vals p w).ell + (vals p w).k)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nm_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Nm.evalRing w =
      (vals p w).Dstar * (vals p w).Dstar - ((vals p w).M * (vals p w).M) *
        (1 + (vals p w).Delta * ((vals p w).c * (vals p w).c)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem At_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).At.evalRing w =
      (vals p w).C * (vals p w).X +
        (vals p w).q * (((p 1 : R) * (vals p w).C - w 1) - (vals p w).bJ * w 3) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Aa_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Aa.evalRing w =
      ((w 12 + (vals p w).V) * (w 12 + (vals p w).V) -
        (w 12 * (vals p w).U) * (w 12 + ((vals p w).V + (vals p w).V))) - 1 := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem As_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).As.evalRing w =
      (w 5 * ((vals p w).c * (vals p w).c)) * (w 5 * ((vals p w).c * (vals p w).c)) - (vals p w).U := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P65Graph

#print axioms P65Graph.output_eq
#print axioms P65Graph.zero_iff
#print axioms P65Graph.A0_eval
#print axioms P65Graph.Nm_eval
#print axioms P65Graph.At_eval
#print axioms P65Graph.Aa_eval
#print axioms P65Graph.As_eval
