import DiophantineConsistency.IPRAQuarticModelBridge
/-! The literal indexed tree quartic preserves existence and nonexistence of
zeros of every finite integer expression in each IΣ₁ model. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQuarticExpressionBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open QuarticCompiler QuarticSyntax AdaptiveEquationSyntax2011 IPRAQuarticModelBridge
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def left {m : ℕ} (e : Expr (Fin m)) : NatExpr (Empty ⊕ Fin m) := (e.rename Sum.inr).splitNatural.1
def right {m : ℕ} (e : Expr (Fin m)) : NatExpr (Empty ⊕ Fin m) := (e.rename Sum.inr).splitNatural.2

theorem exists_zero_iff {m : ℕ} (e : Expr (Fin m)) :
    (∃ v : Fin (witnessCount (left e) (right e) + 1) → V,
      InternalZero (QuarticSyntax.expression (left e) (right e)) v) ↔
    ∃ v : Fin m → V, InternalZero e v := by
  rw [exists_quartic_iff]
  apply exists_congr
  intro v
  change ((e.rename Sum.inr).SemiringZero (Sum.elim Empty.elim v)) ↔ _
  rw [Expr.semiringZero_rename]
  rfl

theorem no_zero_iff {m : ℕ} (e : Expr (Fin m)) :
    (∀ v : Fin (witnessCount (left e) (right e) + 1) → V,
      ¬ InternalZero (QuarticSyntax.expression (left e) (right e)) v) ↔
    ∀ v : Fin m → V, ¬ InternalZero e v := by
  simpa only [not_exists] using not_congr (exists_zero_iff (V := V) e)

#print axioms no_zero_iff
end DiophantineConsistency.IPRAQuarticExpressionBridge
