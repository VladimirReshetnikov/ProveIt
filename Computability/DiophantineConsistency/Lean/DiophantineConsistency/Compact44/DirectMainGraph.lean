import DiophantineConsistency.Compact44.XQ91

/-! Exploratory direct-main expression. Forward polynomial comparison only. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace FreeJDirectMainGraph
open DiophantineConsistency

structure Graph where
  first : Expr (Fin 12)
  main : Expr (Fin 12)
  ordinary : Expr (Fin 12)
  output : Expr (Fin 12)

def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 12) := .var 0
  let F : Expr (Fin 12) := .var 1
  let alpha : Expr (Fin 12) := .var 2
  let t : Expr (Fin 12) := .var 3
  let T : Expr (Fin 12) := .var 4
  let w : Expr (Fin 12) := .var 5
  let s : Expr (Fin 12) := .var 6
  let r : Expr (Fin 12) := .var 7
  let eta : Expr (Fin 12) := .var 8
  let zeta : Expr (Fin 12) := .var 9
  let n : Expr (Fin 12) := .var 10
  let direct : Expr (Fin 12) := .var 11
  let beta : Expr (Fin 12) := .constant (p 0)
  let K0 : Expr (Fin 12) := .constant (p 1)
  let MC : Expr (Fin 12) := .constant (p 2)
  let MF : Expr (Fin 12) := .constant (p 3)
  let qm := J * beta
  let q := 1 + qm
  let X := q * w
  let q2 := q * q
  let q3 := q * q2
  let Y := q3 * s
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
  let kw := K0 + w
  let g27 := C * kw
  let g28 := g27 - F
  let Bt := q * g28
  let g30 := ell + k
  let g31 := g30 + r
  let folded_kBt := k * Bt
  let folded_g31 := g31 - folded_kBt
  let g32 := folded_g31 + s
  let g33 := qm * g32
  let Z := g33 - Bt
  let g38 := Z * Z
  let g39 := qm * qm
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
  let g56 := U * direct
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
  let f := 1 + t
  let f2 := f * f
  let rho := f2 - 1
  let Q := Delta * rho
  let oneQ := 1 - Q
  let den := c2 * c2
  let g73 := T * c
  let g74 := g73 - R
  let g75 := f2 * g74
  let V := g75 - c
  let vn := V + n
  let vn2 := vn * vn
  let polarV2 := V * V
  let polarQV2 := Q * polarV2
  let polarCy := polarQV2 - 1
  let polarHpart := oneQ * vn2
  let h := polarHpart + polarCy
  let polarT := Q * oneQ
  let polarDh := den * h
  let polarA := polarDh - polarT
  let polarA2 := polarA * polarA
  let polarDT := den * polarT
  let polar4DT := 4 * polarDT
  let polarCorrection := polar4DT * polarCy
  let N := polarA2 + polarCorrection
  let A0sq := A0 * A0
  let A1sq := A1 * A1
  let Nsq := N * N
  let sum01 := A0sq + A1sq
  let P12 := sum01 + Nsq
  ⟨A0, A1, N, P12⟩

variable {R : Type*} [CommRing R]

def liftG (v : Fin 12 → R) : Fin 12 → R :=
  Function.update v 11 (v 11 + v 5)

@[simp] theorem liftG_0 (v : Fin 12 → R) : liftG v 0 = v 0 := by
  simp [liftG, show (0 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_1 (v : Fin 12 → R) : liftG v 1 = v 1 := by
  simp [liftG, show (1 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_2 (v : Fin 12 → R) : liftG v 2 = v 2 := by
  simp [liftG, show (2 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_3 (v : Fin 12 → R) : liftG v 3 = v 3 := by
  simp [liftG, show (3 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_4 (v : Fin 12 → R) : liftG v 4 = v 4 := by
  simp [liftG, show (4 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_5 (v : Fin 12 → R) : liftG v 5 = v 5 := by
  simp [liftG, show (5 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_6 (v : Fin 12 → R) : liftG v 6 = v 6 := by
  simp [liftG, show (6 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_7 (v : Fin 12 → R) : liftG v 7 = v 7 := by
  simp [liftG, show (7 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_8 (v : Fin 12 → R) : liftG v 8 = v 8 := by
  simp [liftG, show (8 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_9 (v : Fin 12 → R) : liftG v 9 = v 9 := by
  simp [liftG, show (9 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_10 (v : Fin 12 → R) : liftG v 10 = v 10 := by
  simp [liftG, show (10 : Fin 12) ≠ 11 by decide]
@[simp] theorem liftG_11 (v : Fin 12 → R) : liftG v 11 = v 11 + v 5 := by
  simp [liftG]

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (graph p).first.evalRing (liftG v) = (FreeJXQ91.graph p).first.evalRing v := by
  simp only [graph, FreeJXQ91.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    liftG_0,liftG_1,liftG_2,liftG_3,liftG_4,liftG_5,liftG_6,liftG_7,liftG_8,liftG_9,liftG_10,liftG_11]

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (graph p).main.evalRing (liftG v) = (FreeJXQ91.graph p).main.evalRing v := by
  simp only [graph, FreeJXQ91.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    liftG_0,liftG_1,liftG_2,liftG_3,liftG_4,liftG_5,liftG_6,liftG_7,liftG_8,liftG_9,liftG_10,liftG_11]

theorem ordinary_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (graph p).ordinary.evalRing (liftG v) = (FreeJXQ91.graph p).ordinary.evalRing v := by
  simp only [graph, FreeJXQ91.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    liftG_0,liftG_1,liftG_2,liftG_3,liftG_4,liftG_5,liftG_6,liftG_7,liftG_8,liftG_9,liftG_10,liftG_11]

#print axioms FreeJDirectMainGraph.first_eval
#print axioms FreeJDirectMainGraph.main_eval
#print axioms FreeJDirectMainGraph.ordinary_eval
end FreeJDirectMainGraph
