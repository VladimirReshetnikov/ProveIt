import DiophantineConsistency.Sign17LinesCurrent14Endpoint

/-! SOURCE ONLY. A reviewable named arithmetic transcription at numeral-derived K. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ReadableCurrent14Endpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open ObjectCurrentEquation2011 IPRAStandardTheory IPRACurrentNativeZFC
open IPRAFoundationZFCMappedNegation Sign17LinesCurrent14Endpoint

def displayedExpr (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let S := i * delta * c ^ 2
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let U := S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  let Z := delta * f ^ 2 - S ^ 2
  P * Q * U * W * Z - delta


theorem displayedExpr_eq (p : Fin 4 → ℤ) : displayedExpr p = expressionAt p := by
  rfl

def displayedNoZero : Sentenceᵢ language :=
  let e := positiveShift (displayedExpr linePorts)
  ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))]))

theorem displayedNoZero_eq : displayedNoZero = noZeroAt linePorts := by
  unfold displayedNoZero noZeroAt
  rw [displayedExpr_eq]

theorem displayed_endpoint :
    standardTheory ⊢ displayedNoZero 🡘 ∼mappedNativeRefutation embedding := by
  rw [displayedNoZero_eq]
  exact line_endpoint

end DiophantineConsistency.Sign17ReadableCurrent14Endpoint
#print axioms DiophantineConsistency.Sign17ReadableCurrent14Endpoint.displayedExpr_eq
#print axioms DiophantineConsistency.Sign17ReadableCurrent14Endpoint.displayed_endpoint
