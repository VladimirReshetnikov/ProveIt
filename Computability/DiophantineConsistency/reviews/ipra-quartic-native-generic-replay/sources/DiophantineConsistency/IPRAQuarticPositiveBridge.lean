import DiophantineConsistency.IPRAQuarticExpressionBridge
import DiophantineConsistency.PositiveOffsetArithmetic
import DiophantineConsistency.IPRAQuarticPositiveCore
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQuarticPositiveBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open QuarticCompiler QuarticSyntax AdaptiveEquationSyntax2011 IPRAQuarticExpressionBridge PositiveOffsetArithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem shifted_no_zero_iff {m : ℕ} (e : Expr (Fin m)) :
    (∀ v : Fin (witnessCount (left e) (right e) + 1) → V,
      ¬ InternalZero (positiveShift (rawQuartic e)) v) ↔
    ∀ v : Fin m → V, ¬ InternalZero e v := by
  have h : (∀ v : Fin (witnessCount (left e) (right e) + 1) → V,
      ¬ InternalZero (positiveShift (rawQuartic e)) v) ↔
      ∀ v : Fin (witnessCount (left e) (right e) + 1) → V,
        ¬ InternalZero (QuarticSyntax.expression (left e) (right e)) v := by
    apply forall_congr'
    intro v
    exact not_congr (positiveShift_decrement_zero_iff _ v)
  exact h.trans (no_zero_iff e)
#print axioms shifted_no_zero_iff
end DiophantineConsistency.IPRAQuarticPositiveBridge
