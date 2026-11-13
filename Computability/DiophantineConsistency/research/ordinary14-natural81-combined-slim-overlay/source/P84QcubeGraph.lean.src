import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Source-only proposal. No Lean elaboration or file binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P84QcubeGraph
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
  A0 : Expr (Fin 14)
  A1 : Expr (Fin 14)
  aux : Expr (Fin 14)
  gap : Expr (Fin 14)
  guardResidual : Expr (Fin 14)
  output : Expr (Fin 14)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let f : Expr (Fin 14) := .var 3
  let i : Expr (Fin 14) := .var 4
  let T : Expr (Fin 14) := .var 5
  let w : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let r : Expr (Fin 14) := .var 8
  let eta : Expr (Fin 14) := .var 9
  let zeta : Expr (Fin 14) := .var 10
  let u : Expr (Fin 14) := .var 11
  let gamma : Expr (Fin 14) := .var 12
  let h : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
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
  let M := q3 * qm
  let g26 := X + K0
  let g27 := C * g26
  let guard_base := g27 - F
  let g30 := ell + k
  let g31 := g30 - r
  let Z := M * g31
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
  let shift := g54 - r0
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
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let g78 := V + u
  let y2 := g78 * g78
  let g80 := g78 + V
  let g81 := u * g80
  let g82 := Q * g81
  let Fa := y2 - g82
  let A0sq := A0 * A0
  let A1sq := A1 * A1
  let Fam := Fa - 1
  let Fam2 := Fam * Fam
  let Fsm2 := g72 * g72
  let sum01 := A0sq + A1sq
  let sum23 := Fam2 + Fsm2
  let out := sum01 + sum23
  let bt_quotient := qm * h
  let guard := guard_base - bt_quotient
  let guard2 := guard * guard
  let guarded_out := out + guard2
  -- END LITERAL GRAPH
  ⟨A0, A1, Fa, g72, guard, guarded_out⟩

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (((graph p).A0 * (graph p).A0 + (graph p).A1 * (graph p).A1) +
      (((graph p).aux - 1) * ((graph p).aux - 1) +
        (graph p).gap * (graph p).gap)) +
      ((graph p).guardResidual * (graph p).guardResidual) := by rfl

end P84QcubeGraph

#print axioms P84QcubeGraph.output_shape
