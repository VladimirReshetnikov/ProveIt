import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Literal source-only proposal. No Lean elaboration or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P82NaturalForced
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
  first : Expr (Fin 14)
  main : Expr (Fin 14)
  aux : Expr (Fin 14)
  strong : Expr (Fin 14)
  guardFactor : Expr (Fin 14)
  output : Expr (Fin 14)
  qF : Expr (Fin 14)
  C : Expr (Fin 14)
  G : Expr (Fin 14)
  rank : Expr (Fin 14)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let n_J : Expr (Fin 14) := .var 0
  let n_F : Expr (Fin 14) := .var 1
  let n_alpha : Expr (Fin 14) := .var 2
  let n_f : Expr (Fin 14) := .var 3
  let n_i : Expr (Fin 14) := .var 4
  let n_T : Expr (Fin 14) := .var 5
  let n_w : Expr (Fin 14) := .var 6
  let n_s : Expr (Fin 14) := .var 7
  let n_r : Expr (Fin 14) := .var 8
  let n_eta : Expr (Fin 14) := .var 9
  let n_zeta : Expr (Fin 14) := .var 10
  let n_y : Expr (Fin 14) := .var 11
  let n_gamma : Expr (Fin 14) := .var 12
  let n_h : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let J := n_J + 1
  let alpha := n_alpha + 1
  let i := n_i + 1
  let T := n_T + 1
  let w := n_w + 1
  let s := n_s + 1
  let eta := n_eta + 1
  let gamma := n_gamma + 1
  let qm := J * beta
  let q := 1 + qm
  let X := q * w
  let q2 := q * q
  let q3 := q * q2
  let Y := q3 * s
  let U := Y * q2
  let qF := qm - n_F
  let C := qF - alpha
  let E := X * Y
  let kbase := eta + n_zeta
  let k := kbase + 1
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
  let g26 := X + K0
  let g27 := C * g26
  let guard_base := g27 - n_F
  let g30 := ell + k
  let g38 := n_r * n_r
  let g40 := ell * g30
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let r0 := kbase - R
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
  let f2 := n_f * n_f
  let rho := f2 - 1
  let Q := Delta * rho
  let I := c2 * i
  let g71 := I * I
  let g72 := g71 - Q
  let g74 := T * c
  let g75 := g74 - R
  let g76 := f2 * g75
  let V := g76 - c
  let y2 := n_y * n_y
  let V2 := V * V
  let g81 := y2 - V2
  let g82 := Q * g81
  let Fa := y2 - g82
  let bt_quotient := qm * n_h
  let guard := guard_base - bt_quotient
  let F0 := g38 - g40
  let F1 := 1 + A1
  let Fs := 1 + g72
  let P01 := F0 * F1
  let P012 := P01 * Fa
  let P0123 := P012 * Fs
  let P01234 := P0123 * guard
  let out := P01234 - 1
  -- END LITERAL GRAPH
  ⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).first * (graph p).main * (graph p).aux *
      (graph p).strong * (graph p).guardFactor - 1 := by rfl

end P82NaturalForced

#print axioms P82NaturalForced.output_shape
