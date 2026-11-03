import QCube92

/-! Exploratory 91-gate expression and generic ring comparison. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace FreeJXQ91
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
  let gamma : Expr (Fin 12) := .var 11
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
  let g54 := gamma + w
  let g56 := U * g54
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

def liftX (p : Fin 4 → ℤ) (v : Fin 12 → R) : Fin 12 → R :=
  Function.update v 5 ((1 + v 0 * (p 0 : R)) * v 5)

@[simp] theorem liftX_0 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 0 = v 0 := by
  simp [liftX, show (0 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_1 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 1 = v 1 := by
  simp [liftX, show (1 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_2 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 2 = v 2 := by
  simp [liftX, show (2 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_3 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 3 = v 3 := by
  simp [liftX, show (3 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_4 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 4 = v 4 := by
  simp [liftX, show (4 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_5 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 5 = (1 + v 0 * (p 0 : R)) * v 5 := by simp [liftX]
@[simp] theorem liftX_6 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 6 = v 6 := by
  simp [liftX, show (6 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_7 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 7 = v 7 := by
  simp [liftX, show (7 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_8 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 8 = v 8 := by
  simp [liftX, show (8 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_9 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 9 = v 9 := by
  simp [liftX, show (9 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_10 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 10 = v 10 := by
  simp [liftX, show (10 : Fin 12) ≠ 5 by decide]
@[simp] theorem liftX_11 (p : Fin 4 → ℤ) (v : Fin 12 → R) : liftX p v 11 = v 11 := by
  simp [liftX, show (11 : Fin 12) ≠ 5 by decide]

/-- The source transport block has a common q factor. -/
theorem factor_bt (q c w K F : R) :
    c * (q*w + K*q) - F*q = q * (c*(K+w)-F) := by ring

/-- With Y=q³s, the two mixed main-root terms have a common U factor. -/
theorem factor_main (q q3 s w gamma : R) :
    ((q3*s)*(q*q))*gamma + ((q*w)*(q3*s))*q =
      ((q3*s)*(q*q))*(gamma+w) := by ring

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (FreeJQCube92.graph p).first.evalRing (liftX p v) = (graph p).first.evalRing v := by
  simp only [FreeJQCube92.graph, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    liftX_0,liftX_1,liftX_2,liftX_3,liftX_4,liftX_5,liftX_6,liftX_7,liftX_8,liftX_9,liftX_10,liftX_11]
  simp only [factor_bt]

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (FreeJQCube92.graph p).main.evalRing (liftX p v) = (graph p).main.evalRing v := by
  simp only [FreeJQCube92.graph, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    liftX_0,liftX_1,liftX_2,liftX_3,liftX_4,liftX_5,liftX_6,liftX_7,liftX_8,liftX_9,liftX_10,liftX_11]
  simp only [factor_main]

theorem ordinary_eval (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    (FreeJQCube92.graph p).ordinary.evalRing (liftX p v) = (graph p).ordinary.evalRing v := by
  simp only [FreeJQCube92.graph, graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    liftX_0,liftX_1,liftX_2,liftX_3,liftX_4,liftX_5,liftX_6,liftX_7,liftX_8,liftX_9,liftX_10,liftX_11]

#print axioms FreeJXQ91.first_eval
#print axioms FreeJXQ91.main_eval
#print axioms FreeJXQ91.ordinary_eval
end FreeJXQ91
