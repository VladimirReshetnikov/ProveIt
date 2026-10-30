import DiophantineConsistency.AdaptiveDirectOrdinate86Literal

/-! Generated 85-gate literal and conditional two-hole binding. The new
positive witness bound needed for an unconditional equivalence is not proved. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Literal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context ArithmeticSignedPairs

def expressionAt85 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let C : Expr (Fin 13) := .var 2
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
  let g44 := qF * q
  let G := g44 - C
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

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Option (Fin 13))) :=
  let J : Expr (Option (Option (Fin 13))) := .var (some (some 0))
  let F : Expr (Option (Option (Fin 13))) := .var (some (some 1))
  let f : Expr (Option (Option (Fin 13))) := .var (some (some 3))
  let i : Expr (Option (Option (Fin 13))) := .var (some (some 4))
  let T : Expr (Option (Option (Fin 13))) := .var (some (some 5))
  let X : Expr (Option (Option (Fin 13))) := .var (some (some 6))
  let Y : Expr (Option (Option (Fin 13))) := .var (some (some 7))
  let r : Expr (Option (Option (Fin 13))) := .var (some (some 8))
  let eta : Expr (Option (Option (Fin 13))) := .var (some (some 9))
  let zeta : Expr (Option (Option (Fin 13))) := .var (some (some 10))
  let y : Expr (Option (Option (Fin 13))) := .var (some (some 11))
  let gamma : Expr (Option (Option (Fin 13))) := .var (some (some 12))
  let beta : Expr (Option (Option (Fin 13))) := .constant (p 0)
  let K0 : Expr (Option (Option (Fin 13))) := .constant (p 1)
  let MC : Expr (Option (Option (Fin 13))) := .constant (p 2)
  let MF : Expr (Option (Option (Fin 13))) := .constant (p 3)
  let C : Expr (Option (Option (Fin 13))) := .var none
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
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
  let G : Expr (Option (Option (Fin 13))) := .var (some none)
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

def embed (i : Fin 13) : Fin 14 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def oldLift (i : Fin 13) : Expr (Fin 14) :=
  if i = 2 then .var 13 else .var (embed i)
def newLift (i : Fin 13) : Expr (Fin 14) := .var (embed i)
def qExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := 1 + .var 0 * .constant (p 0)
def qmExpr (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 0 * .constant (p 0)
def oldGap (p : Fin 4 → ℤ) : Expr (Fin 14) := qExpr p - .var 1 - .var 13
def newGap : Expr (Fin 14) := .var 2
def oldRank (p : Fin 4 → ℤ) : Expr (Fin 14) := .var 13 + (qExpr p - .var 1) * qmExpr p
def newRank (p : Fin 4 → ℤ) : Expr (Fin 14) := (qExpr p - .var 1) * qExpr p - .var 2

def oldFill (p : Fin 4 → ℤ) : Option (Option (Fin 13)) → Expr (Fin 14)
  | none => oldGap p
  | some none => oldRank p
  | some (some i) => .var (embed i)
def newFill (p : Fin 4 → ℤ) : Option (Option (Fin 13)) → Expr (Fin 14)
  | none => newGap
  | some none => newRank p
  | some (some i) => .var (embed i)

theorem old_as_context (p : Fin 4 → ℤ) :
    (AdaptiveDirectOrdinate86Literal.expressionAt86 p).subst oldLift =
      (contextAt p).subst (oldFill p) := by
  rfl

theorem new_as_context (p : Fin 4 → ℤ) :
    (expressionAt85 p).subst newLift = (contextAt p).subst (newFill p) := by
  rfl

/-- The two actual literals have the same zero test when both corresponding
signed subexpressions are equivalent. No positivity bound is asserted. -/
theorem conditional_literal_zero_iff {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hg : Equivalent (splitEval (oldGap p) v) (splitEval newGap v))
    (hr : Equivalent (splitEval (oldRank p) v) (splitEval (newRank p) v)) :
    (splitEval ((AdaptiveDirectOrdinate86Literal.expressionAt86 p).subst oldLift) v).1 =
      (splitEval ((AdaptiveDirectOrdinate86Literal.expressionAt86 p).subst oldLift) v).2 ↔
    (splitEval ((expressionAt85 p).subst newLift) v).1 =
      (splitEval ((expressionAt85 p).subst newLift) v).2 := by
  rw [old_as_context,new_as_context]
  apply equivalent_zero_iff
  apply splitEval_subst_equiv
  intro i
  cases i with
  | none => exact hg
  | some j =>
    cases j with
    | none => exact hr
    | some j => exact equivalent_refl _
end DiophantineConsistency.AdaptiveGap85Literal
