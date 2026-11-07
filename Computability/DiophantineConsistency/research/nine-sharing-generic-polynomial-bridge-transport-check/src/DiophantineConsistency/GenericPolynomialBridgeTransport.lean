import DiophantineConsistency.HAExpressionAssembly
import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! SOURCE-ONLY: generic model-zero equivalence transports a polynomial bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.GenericPolynomialBridgeTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

theorem transfer {m n : ℕ} (e : Expr (Fin m)) (f : Expr (Fin n))
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      (∃ w : Fin m → V, InternalZero e w) ↔ ∃ w : Fin n → V, InternalZero f w)
    (hb : HAExpressionAssembly.PolynomialBridge f) : HAExpressionAssembly.PolynomialBridge e := by
  intro V _ _
  have hf := hb V
  rw [HAExpressionAssembly.classicalNoZero_iff] at hf ⊢
  rw [← hf]
  simpa only [InternalZero, not_exists, ne_eq] using not_congr (h V)
end DiophantineConsistency.GenericPolynomialBridgeTransport
#print axioms DiophantineConsistency.GenericPolynomialBridgeTransport.transfer
