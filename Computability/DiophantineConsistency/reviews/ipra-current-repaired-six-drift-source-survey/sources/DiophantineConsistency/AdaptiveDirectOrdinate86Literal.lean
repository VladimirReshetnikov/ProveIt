import DiophantineConsistency.AdaptiveFirstRootFactor87Literal
import DiophantineConsistency.AdaptiveDirectOrdinate86Context

/-! Generated direct-ordinate literal and conditional one-hole binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Literal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context ArithmeticSignedPairs

def expressionAt86 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
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
  let y : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let beta : Expr (Fin 13) := .constant (p 0)
  let K0 : Expr (Fin 13) := .constant (p 1)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
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
  let root_skew := k * Bt
  let root_inner := g31 - root_skew
  let root_scaled := M * root_inner
  let g33 := Y * qm
  let root_btq3 := Bt * q3
  let root_sum := root_scaled + g33
  let Z := root_sum - root_btq3
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
  let y2 := y * y
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
  P13

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 13)) :=
  let J : Expr (Option (Fin 13)) := .var (some 0)
  let F : Expr (Option (Fin 13)) := .var (some 1)
  let alpha : Expr (Option (Fin 13)) := .var (some 2)
  let f : Expr (Option (Fin 13)) := .var (some 3)
  let i : Expr (Option (Fin 13)) := .var (some 4)
  let T : Expr (Option (Fin 13)) := .var (some 5)
  let X : Expr (Option (Fin 13)) := .var (some 6)
  let Y : Expr (Option (Fin 13)) := .var (some 7)
  let r : Expr (Option (Fin 13)) := .var (some 8)
  let eta : Expr (Option (Fin 13)) := .var (some 9)
  let zeta : Expr (Option (Fin 13)) := .var (some 10)
  let gamma : Expr (Option (Fin 13)) := .var (some 12)
  let beta : Expr (Option (Fin 13)) := .constant (p 0)
  let K0 : Expr (Option (Fin 13)) := .constant (p 1)
  let MC : Expr (Option (Fin 13)) := .constant (p 2)
  let MF : Expr (Option (Fin 13)) := .constant (p 3)
  let y2 : Expr (Option (Fin 13)) := .var none
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
  let root_skew := k * Bt
  let root_inner := g31 - root_skew
  let root_scaled := M * root_inner
  let g33 := Y * qm
  let root_btq3 := Bt * q3
  let root_sum := root_scaled + g33
  let Z := root_sum - root_btq3
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
  P13

def signedV (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let f : Expr (Fin 14) := .var 3
  let T : Expr (Fin 14) := .var 5
  let Y : Expr (Fin 14) := .var 7
  let eta : Expr (Fin 14) := .var 9
  let zeta : Expr (Fin 14) := .var 10
  let beta : Expr (Fin 14) := .constant (p 0)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let qF := q - F
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let f2 := f * f
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  V

def embed (i : Fin 13) : Fin 14 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def oldLift (i : Fin 13) : Expr (Fin 14) :=
  if i = 11 then .var 13 else .var (embed i)
def newLift (i : Fin 13) : Expr (Fin 14) := .var (embed i)
def fill (e : Expr (Fin 14)) : Option (Fin 13) → Expr (Fin 14)
  | none => e
  | some i => .var (embed i)

def oldSquare (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let y := signedV p + .var 13
  y*y
def newSquare : Expr (Fin 14) :=
  let y : Expr (Fin 14) := .var 11
  y*y

theorem old_as_context (p : Fin 4 → ℤ) :
    (AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift =
      (contextAt p).subst (fill (oldSquare p)) := by
  rfl

theorem new_as_context (p : Fin 4 → ℤ) :
    (expressionAt86 p).subst newLift =
      (contextAt p).subst (fill newSquare) := by
  rfl

/-- With equivalent squared ordinates, the actual literal zero tests agree. -/
theorem conditional_literal_zero_iff {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (h : Equivalent (splitEval (oldSquare p) v) (splitEval newSquare v)) :
    (splitEval ((AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift) v).1 =
      (splitEval ((AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift) v).2 ↔
    (splitEval ((expressionAt86 p).subst newLift) v).1 =
      (splitEval ((expressionAt86 p).subst newLift) v).2 := by
  rw [old_as_context,new_as_context]
  apply equivalent_zero_iff
  apply splitEval_subst_equiv
  intro i
  cases i with
  | none => exact h
  | some i => exact equivalent_refl _

def expression86 : Expr (Fin 13) := expressionAt86 CurrentWindowCarry2011.ports
def naturalExpression86 : Expr (Fin 13) := AdaptiveEquationSyntax2011.positiveShift expression86

end DiophantineConsistency.AdaptiveDirectOrdinate86Literal
