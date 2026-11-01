import DiophantineConsistency.AdaptiveGap85ShiftFirstInput
import DiophantineConsistency.AdaptiveGap85ShiftMainShift
import DiophantineConsistency.AdaptiveDirectOrdinate86Lift

/-! A common three-hole context for the exact 85 literal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftContext
open AdaptiveGap85Literal AdaptiveGap85ShiftFirstInput AdaptiveGap85ShiftMainShift AdaptiveGap85ShiftAuxInput
def contextFactors (p : Fin 4 → ℤ) : Expr (Option (Option (Option (Fin 13)))) × Expr (Option (Option (Option (Fin 13)))) × Expr (Option (Option (Option (Fin 13)))) × Expr (Option (Option (Option (Fin 13)))) :=
  let J : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 0)))
  let F : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 1)))
  let C : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 2)))
  let f : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 3)))
  let i : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 4)))
  let T : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 5)))
  let X : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 6)))
  let Y : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 7)))
  let r : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 8)))
  let eta : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 9)))
  let zeta : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 10)))
  let y : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 11)))
  let gamma : Expr (Option (Option (Option (Fin 13)))) := .var (some (some (some 12)))
  let beta : Expr (Option (Option (Option (Fin 13)))) := .constant (p 0)
  let K0 : Expr (Option (Option (Option (Fin 13)))) := .constant (p 1)
  let MC : Expr (Option (Option (Option (Fin 13)))) := .constant (p 2)
  let MF : Expr (Option (Option (Option (Fin 13)))) := .constant (p 3)
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
  let Z : Expr (Option (Option (Option (Fin 13)))) := .var none
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
  let shift : Expr (Option (Option (Option (Fin 13)))) := .var (some none)
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
  let V : Expr (Option (Option (Option (Fin 13)))) := .var (some (some none))
  let y2 := y * y
  let g80 := V * V
  let g81 := y2 - g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let F0 := 1 + A0
  let F1 := 1 + A1
  (F0,F1,Fa,Fs)


def contextAt (p : Fin 4 → ℤ) : Expr (Option (Option (Option (Fin 13)))) :=
  let f := contextFactors p
  f.2.2.2*(f.2.2.1*(f.1*f.2.1))-1

def fill (p : Fin 4 → ℤ) : Option (Option (Option (Fin 13))) → Expr (Fin 13)
  | none => firstInput p
  | some none => mainShift p
  | some (some none) => auxiliaryInput p
  | some (some (some i)) => if i=2 ∨ i=5 ∨ i=8 ∨ i=12 then .constant 0 else .var i

/-- The three named inputs are exactly the varying literal subexpressions. -/
theorem literal_as_context (p : Fin 4 → ℤ) :
    (contextAt p).subst (fill p)=expressionAt85 p := by
  rfl
end DiophantineConsistency.AdaptiveGap85ShiftContext
