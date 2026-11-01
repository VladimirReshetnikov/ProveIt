import DiophantineConsistency.HAAdaptiveDirectOrdinate86

/-! Same-valuation model equivalence transports the generic polynomial bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.HAExpressionSameZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HAExpressionAssembly AdaptiveEquationSyntax2011 FoundationHANoZero

def SameZero {n : ℕ} (e f : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∀ v : Fin n → V, InternalZero e v ↔ InternalZero f v

theorem shifted {n : ℕ} (e f : Expr (Fin n)) (h : SameZero e f) :
    SameZero (positiveShift e) (positiveShift f) := by
  intro V _ _ v
  rw [internalZero_positiveShift, internalZero_positiveShift]
  exact h V _

theorem bridge {n : ℕ} (e f : Expr (Fin n)) (h : SameZero e f)
    (hf : PolynomialBridge f) : PolynomialBridge e := by
  intro V _ _
  have eqv : (classicalNoZero e).Evalb (M := V) ![] ↔
      (classicalNoZero f).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin n → V => not_congr (h V v))
  exact eqv.trans (hf V)

theorem bridge86 (e : Expr (Fin 13))
    (h : SameZero e AdaptiveDirectOrdinate86Literal.naturalExpression86) : PolynomialBridge e :=
  bridge e _ h HAAdaptiveDirectOrdinate86.polynomialBridge
end DiophantineConsistency.HAExpressionSameZero
