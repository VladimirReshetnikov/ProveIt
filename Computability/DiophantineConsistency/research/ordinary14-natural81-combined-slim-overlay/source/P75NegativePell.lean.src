import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Literal source-only proposal. No Lean elaboration, binding or endpoint claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P75NegativePell
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
  first : Expr (Fin 14)
  main : Expr (Fin 14)
  aux : Expr (Fin 14)
  strong : Expr (Fin 14)
  guardFactor : Expr (Fin 14)
  output : Expr (Fin 14)
  b : Expr (Fin 14)
  q : Expr (Fin 14)
  X : Expr (Fin 14)
  Y : Expr (Fin 14)
  k : Expr (Fin 14)
  ell : Expr (Fin 14)
  a : Expr (Fin 14)
  c : Expr (Fin 14)
  U : Expr (Fin 14)
  Dstar : Expr (Fin 14)
  Q : Expr (Fin 14)
  I : Expr (Fin 14)
  vroot : Expr (Fin 14)
  C : Expr (Fin 14)

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
  let y : Expr (Fin 14) := .var 11
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
  let g26 := X + K0
  let g27 := C * g26
  let guard_base := g27 - F
  let g30 := ell + k
  let g38 := r * r
  let g40 := ell * g30
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
  let y2 := y * y
  let V2 := V * V
  let g81 := y2 - V2
  let g82 := Q * g81
  let Fa := y2 - g82
  let bt_quotient := qm * h
  let guard := guard_base - bt_quotient
  let F0 := g38 - g40
  let F1 := 1 + A1
  let Fs := 1 + g72
  let Fg := 1 + guard
  let P01 := F0 * F1
  let P012 := P01 * Fa
  let P0123 := P012 * Fs
  let P01234 := P0123 * Fg
  let out := P01234 - 1
  -- END LITERAL GRAPH
  ⟨F0, F1, Fa, Fs, Fg, out, qm, q, X, Y, k, ell, a, c, U, Dstar, Q, I, V, C⟩

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).first * (graph p).main * (graph p).aux *
      (graph p).strong * (graph p).guardFactor - 1 := by rfl

end P75NegativePell

#print axioms P75NegativePell.output_shape
