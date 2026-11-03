import DiophantineConsistency.ArithmeticRepresentation
import DiophantineConsistency.ModelArithmetic

/-! # Internal correctness of Diophantine representation data

A `Rep σ P` is finite syntax certified against a predicate `P` on natural
valuations. `Holds r Q` states that the same syntax is correct inside every
model of `𝗜𝚺₁` for a model-uniform predicate `Q`: a valuation satisfies `Q`
exactly when some model witnesses make the expression vanish. `GraphHolds`
is the specialisation to graph representations of model-uniform functions.

These are the interface statements for internalizing the scalar primitive
recursive compiler (`ScalarPRCode.graphRep`) that produces the source of the
nine-variable equation `ExplicitZFC.expression`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelRep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

/-- A predicate on valuations in an arbitrary model of `𝗜𝚺₁`. -/
abbrev ModelPred (σ : Type*) :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], (σ → V) → Prop

/-- A function on valuations in an arbitrary model of `𝗜𝚺₁`. -/
abbrev ModelFun (σ : Type*) :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], (σ → V) → V

/-- The representation is internally correct for `Q`. -/
def Holds {σ : Type*} {P : (σ → ℕ) → Prop} (r : Rep σ P) (Q : ModelPred σ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (v : σ → V),
    Q V v ↔ ∃ w : Fin r.witnessCount → V,
      AdaptiveEquationSyntax2011.InternalZero r.expression (Sum.elim v w)

/-- The graph representation is internally correct for the function `F`. -/
def GraphHolds {σ : Type*} {f : (σ → ℕ) → ℕ} (r : GraphRep f) (F : ModelFun σ) : Prop :=
  Holds r (fun V _ _ v => v none = F V (fun i => v (some i)))

/-- Changing the certified predicate changes no syntax. -/
theorem holds_ofIff {σ : Type*} {P P' : (σ → ℕ) → Prop} (r : Rep σ P) (h : ∀ v, P v ↔ P' v)
    (Q : ModelPred σ) : Holds (r.ofIff h) Q ↔ Holds r Q := Iff.rfl

/-- Internal correctness transfers along an internally equivalent predicate. -/
theorem holds_congr {σ : Type*} {P : (σ → ℕ) → Prop} (r : Rep σ P) {Q Q' : ModelPred σ}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (v : σ → V), Q V v ↔ Q' V v)
    (hr : Holds r Q) : Holds r Q' := by
  intro V _ _ v
  exact (h V v).symm.trans (hr V v)

end DiophantineConsistency.ModelRep
