import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.NaturalExpressionSemiring

/-! Literal adaptive expression in the accepted thirteen-coordinate gate order.
The split-natural equation is meaningful in every commutative semiring. -/
set_option Elab.async false
namespace DiophantineConsistency.AdaptiveEquationSyntax2011

/-- The four ports are integer leaves; the high-port shift is in the tuple. -/
def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 13) :=
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
  let g22 := k * qm
  let W := 1 + g22
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let g32 := M * g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let g35 := W * q3
  let g36 := Bt * g35
  let Z := g34 - g36
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

def expression : Expr (Fin 13) := expressionAt CurrentWindowCarry2011.ports

def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=
  e.subst (fun i => Expr.var i + Expr.constant 1)

def naturalExpression : Expr (Fin 13) := positiveShift expression

def InternalZero {σ R : Type*} [CommSemiring R] (e : Expr σ) (v : σ → R) : Prop :=
  e.splitNatural.1.evalSemiring v = e.splitNatural.2.evalSemiring v

theorem split_positiveShift {σ R : Type*} [CommSemiring R] (e : Expr σ) (v : σ → R) :
    ((positiveShift e).splitNatural.1.evalSemiring v,
      (positiveShift e).splitNatural.2.evalSemiring v) =
      (e.splitNatural.1.evalSemiring (fun i => v i + 1),
       e.splitNatural.2.evalSemiring (fun i => v i + 1)) := by
  induction e <;> simp_all [positiveShift, Expr.subst, Expr.splitNatural, NatExpr.evalSemiring]

theorem internalZero_positiveShift {σ R : Type*} [CommSemiring R] (e : Expr σ) (v : σ → R) :
    InternalZero (positiveShift e) v ↔ InternalZero e (fun i => v i + 1) :=
  Iff.of_eq (congrArg (fun p : R × R => p.1 = p.2) (split_positiveShift e v))

theorem current_zero_shift {R : Type*} [CommSemiring R] (v : Fin 13 → R) :
    InternalZero naturalExpression v ↔ InternalZero expression (fun i => v i + 1) :=
  internalZero_positiveShift expression v

end DiophantineConsistency.AdaptiveEquationSyntax2011
