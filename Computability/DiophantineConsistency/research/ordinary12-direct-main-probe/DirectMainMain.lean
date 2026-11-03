import DirectMainGraph
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! Extract the main Pell norm from a direct-main graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DirectMainMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveQuotients2011
open ArithmeticAdaptiveFactorMagnitude2011

def mainParts (p : Fin 4 → ℤ) : Expr (Fin 12) × Expr (Fin 12) :=
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
  (Dstar, g65)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)

theorem main_shape (p : Fin 4 → ℤ) : (graph p).main =
    (mainParts p).1*(mainParts p).1-(mainParts p).2 := by rfl

theorem rhs_pair (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let U : V := Y*(q*q)
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let H : V := 3+4*a
    pairEval (mainParts (integerPorts p)).2 v = (U*U*(1+(H+a*a)*(c*c)),0) := by
  simp [mainParts,integerPorts,pairEval,Expr.splitNatural,NatExpr.evalSemiring]

theorem main_zero (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    InternalZero (graph (integerPorts p)).main v := by
  rw [internalZero_iff] at hz ⊢
  change (graph (integerPorts p)).main.evalRing (fun j => ι (v j)) = 0
  have hshape : (graph (integerPorts p)).output =
      (graph (integerPorts p)).first*(graph (integerPorts p)).first+
      (graph (integerPorts p)).main*(graph (integerPorts p)).main+
      (graph (integerPorts p)).ordinary*(graph (integerPorts p)).ordinary := by rfl
  rw [hshape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_mul] at hz
  have ha := sq_nonneg ((graph (integerPorts p)).first.evalRing (fun j => ι (v j)))
  have hb := sq_nonneg ((graph (integerPorts p)).main.evalRing (fun j => ι (v j)))
  have hc := sq_nonneg ((graph (integerPorts p)).ordinary.evalRing (fun j => ι (v j)))
  have h : (graph (integerPorts p)).main.evalRing (fun j => ι (v j)) *
      (graph (integerPorts p)).main.evalRing (fun j => ι (v j)) = 0 := by nlinarith
  exact mul_self_eq_zero.mp h

theorem main_scaled_norm (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let U : V := Y*(q*q)
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let H : V := 3+4*a
    magnitude (pairEval (mainParts (integerPorts p)).1 v) *
      magnitude (pairEval (mainParts (integerPorts p)).1 v) = U*U*(1+(H+a*a)*(c*c)) := by
  have hf := main_zero p v hz
  rw [main_shape] at hf
  have hunit : (pairEval (1+((mainParts (integerPorts p)).1*(mainParts (integerPorts p)).1-
      (mainParts (integerPorts p)).2)) v).1 =
      (pairEval (1+((mainParts (integerPorts p)).1*(mainParts (integerPorts p)).1-
      (mainParts (integerPorts p)).2)) v).2+1 := by
    have h := congrArg (fun z : V => z+1) hf
    simpa [InternalZero,pairEval,Expr.splitNatural,NatExpr.evalSemiring,add_assoc,add_comm,add_left_comm] using h
  have hs := unit_square_norm (mainParts (integerPorts p)).1 (mainParts (integerPorts p)).2 v hunit
  rw [rhs_pair p v] at hs
  simpa only [Prod.fst,Prod.snd,add_zero] using hs

#print axioms DirectMainMain.main_zero
#print axioms DirectMainMain.main_scaled_norm
end DirectMainMain
