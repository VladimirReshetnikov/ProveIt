import DiophantineConsistency.IPRAAxiomPartition
import DiophantineConsistency.IPRANativeEquationImages
/-! Induction, defining equations and successor-nonzero images are proved.
Equality, successor injectivity, order, classical comparison and consistency
identification remain explicit premises. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAAxiomReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory

theorem axiom_images_from_equality_and_basic
    (heq : ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (hinj : IPRANativeTheory.nativeTheory ⊢ succInjectiveᴺ)
    (horder : IPRANativeTheory.nativeTheory ⊢ orderDefinitionᴺ) :
    ∀ σ ∈ PRA, IPRANativeTheory.nativeTheory ⊢ σᴺ := by
  apply IPRAAxiomPartition.axiom_images_from_remaining heq
  · intro σ hσ
    exact IPRANativeEquationImages.definingEquation_image hσ
  · intro σ hσ
    cases hσ with
    | succNonzero => exact IPRANativeAxiomImage.succNonzero_image
    | succInjective => exact hinj
    | orderDefinition => exact horder

theorem mapped_noZero_from_equality_and_basic
    (heq : ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (hinj : IPRANativeTheory.nativeTheory ⊢ succInjectiveᴺ)
    (horder : IPRANativeTheory.nativeTheory ⊢ orderDefinitionᴺ)
    (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (ψ : Sentence language) (target : Sentenceᵢ language)
    (h : PRA ⊢ (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b)) 🡘 ∼ψ)
    (hcons : IPRANativeTheory.nativeTheory ⊢ (∼ψᴺ) 🡘 target) :
    IPRANativeTheory.nativeTheory ⊢
      (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![Semiterm.lMap embedding a, Semiterm.lMap embedding b]))) 🡘 target :=
  IPRAConditionalComparison.mapped_noZero_comparison_with_target
    (axiom_images_from_equality_and_basic heq hinj horder) n a b ψ target h hcons
end DiophantineConsistency.IPRAAxiomReduction
