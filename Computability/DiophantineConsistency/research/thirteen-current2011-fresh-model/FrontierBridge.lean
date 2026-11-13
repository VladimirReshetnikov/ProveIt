import FreshCarrierSpheres

/-! Local no-zero transport lemmas using the already built current-base model
provider. These names match the original sources; no historical bridge module
is imported. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.HAExpressionNoZeroEquiv
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HAExpressionAssembly AdaptiveEquationSyntax2011 FoundationHANoZero

def SameNoZero {n m : ℕ} (e : Expr (Fin n)) (f : Expr (Fin m)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∀ v : Fin n → V, ¬InternalZero e v) ↔ ∀ v : Fin m → V, ¬InternalZero f v

theorem bridge {n m : ℕ} (e : Expr (Fin n)) (f : Expr (Fin m))
    (h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e := by
  intro V _ _
  have eqv : (classicalNoZero e).Evalb (M := V) ![] ↔
      (classicalNoZero f).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using h V
  exact eqv.trans (hf V)
end DiophantineConsistency.HAExpressionNoZeroEquiv

namespace DiophantineConsistency.HAExpressionSameZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HAExpressionAssembly AdaptiveEquationSyntax2011 FoundationHANoZero

theorem bridge {n : ℕ} (e f : Expr (Fin n))
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      ∀ v : Fin n → V, InternalZero e v ↔ InternalZero f v)
    (hf : PolynomialBridge f) : PolynomialBridge e := by
  intro V _ _
  have eqv : (classicalNoZero e).Evalb (M := V) ![] ↔
      (classicalNoZero f).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin n → V => not_congr (h V v))
  exact eqv.trans (hf V)
end DiophantineConsistency.HAExpressionSameZero
