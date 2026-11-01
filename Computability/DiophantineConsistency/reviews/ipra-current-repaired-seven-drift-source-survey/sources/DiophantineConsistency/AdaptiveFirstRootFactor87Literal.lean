import DiophantineConsistency.AdaptiveEquationSyntax2011
import DiophantineConsistency.AdaptiveFirstRootFactor87Context

/-! Generated 87-row adaptive output and a shared one-hole context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveFirstRootFactor87Literal
open DiophantineConsistency.AdaptiveFirstRootFactor87Syntax
open DiophantineConsistency.AdaptiveFirstRootFactor87Context

structure RootInputs (σ : Type*) where
  q3 : Expr σ
  qm : Expr σ
  k : Expr σ
  bt : Expr σ
  g : Expr σ
  y : Expr σ

def rootInputsAt (p : Fin 4 → ℤ) : RootInputs (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let X : Expr (Fin 13) := .var 6
  let Y : Expr (Fin 13) := .var 7
  let r : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let beta : Expr (Fin 13) := .constant (p 0)
  let K0 : Expr (Fin 13) := .constant (p 1)
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let ell := E * kY
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  ⟨q3, qm, k, Bt, g31, Y⟩

def contextAt (p : Fin 4 → ℤ) : Expr (Option (Fin 13)) :=
  let J : Expr (Option (Fin 13)) := .var (some 0)
  let F : Expr (Option (Fin 13)) := .var (some 1)
  let alpha : Expr (Option (Fin 13)) := .var (some 2)
  let f : Expr (Option (Fin 13)) := .var (some 3)
  let i : Expr (Option (Fin 13)) := .var (some 4)
  let T : Expr (Option (Fin 13)) := .var (some 5)
  let X : Expr (Option (Fin 13)) := .var (some 6)
  let Y : Expr (Option (Fin 13)) := .var (some 7)
  let eta : Expr (Option (Fin 13)) := .var (some 9)
  let zeta : Expr (Option (Fin 13)) := .var (some 10)
  let u : Expr (Option (Fin 13)) := .var (some 11)
  let gamma : Expr (Option (Fin 13)) := .var (some 12)
  let beta : Expr (Option (Fin 13)) := .constant (p 0)
  let MC : Expr (Option (Fin 13)) := .constant (p 2)
  let MF : Expr (Option (Fin 13)) := .constant (p 3)
  let Z : Expr (Option (Fin 13)) := .var none
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
  let g30 := ell + k
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
  let g78 := V + u
  let y2 := g78 * g78
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

def expressionAt87 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
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
  let u : Expr (Fin 13) := .var 11
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
  let g78 := V + u
  let y2 := g78 * g78
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

theorem maintained_as_context (p : Fin 4 → ℤ) :
    AdaptiveEquationSyntax2011.expressionAt p =
      (contextAt p).subst (oldFill (rootInputsAt p).q3 (rootInputsAt p).qm
        (rootInputsAt p).k (rootInputsAt p).bt (rootInputsAt p).g (rootInputsAt p).y) := by
  rfl

theorem candidate_as_context (p : Fin 4 → ℤ) :
    expressionAt87 p =
      (contextAt p).subst (newFill (rootInputsAt p).q3 (rootInputsAt p).qm
        (rootInputsAt p).k (rootInputsAt p).bt (rootInputsAt p).g (rootInputsAt p).y) := by
  rfl

/-- The maintained and candidate expressions have identical split values. -/
theorem split_expression_eq {R : Type*} [CommSemiring R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    splitEval (AdaptiveEquationSyntax2011.expressionAt p) v = splitEval (expressionAt87 p) v := by
  rw [maintained_as_context, candidate_as_context]
  exact root_context_split (contextAt p) (rootInputsAt p).q3 (rootInputsAt p).qm
    (rootInputsAt p).k (rootInputsAt p).bt (rootInputsAt p).g (rootInputsAt p).y v

def expression87 : Expr (Fin 13) := expressionAt87 CurrentWindowCarry2011.ports
def naturalExpression87 : Expr (Fin 13) := AdaptiveEquationSyntax2011.positiveShift expression87

/-- The actual positive-shifted equations are equivalent in every commutative semiring. -/
theorem current_natural_zero_iff {R : Type*} [CommSemiring R] (v : Fin 13 → R) :
    AdaptiveEquationSyntax2011.InternalZero AdaptiveEquationSyntax2011.naturalExpression v ↔
      AdaptiveEquationSyntax2011.InternalZero naturalExpression87 v := by
  change AdaptiveEquationSyntax2011.InternalZero
      (AdaptiveEquationSyntax2011.positiveShift AdaptiveEquationSyntax2011.expression) v ↔
    AdaptiveEquationSyntax2011.InternalZero (AdaptiveEquationSyntax2011.positiveShift expression87) v
  rw [AdaptiveEquationSyntax2011.internalZero_positiveShift,
    AdaptiveEquationSyntax2011.internalZero_positiveShift]
  change (splitEval (AdaptiveEquationSyntax2011.expressionAt CurrentWindowCarry2011.ports)
      (fun i => v i + 1)).1 =
      (splitEval (AdaptiveEquationSyntax2011.expressionAt CurrentWindowCarry2011.ports)
      (fun i => v i + 1)).2 ↔
    (splitEval (expressionAt87 CurrentWindowCarry2011.ports) (fun i => v i + 1)).1 =
      (splitEval (expressionAt87 CurrentWindowCarry2011.ports) (fun i => v i + 1)).2
  exact Iff.of_eq (congrArg (fun xy : R × R => xy.1 = xy.2)
    (split_expression_eq CurrentWindowCarry2011.ports (fun i => v i + 1)))

end DiophantineConsistency.AdaptiveFirstRootFactor87Literal
