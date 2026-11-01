import DiophantineConsistency.IPRAAxiomReduction
import DiophantineConsistency.IPRANativeBasicImages
import DiophantineConsistency.IPRAEqualityReflGG
/-! Native iPRA proves all induction, defining-equation and basic-axiom
images. Equality and the consistency bridge remain explicit premises. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAEqualityRemaining
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory

theorem axiom_images_from_equality
    (heq : ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ) :
    ∀ σ ∈ PRA, IPRANativeTheory.nativeTheory ⊢ σᴺ :=
  IPRAAxiomReduction.axiom_images_from_equality_and_basic heq
    IPRANativeBasicImages.succInjective_image IPRANativeBasicImages.orderDefinition_image

theorem mapped_noZero_from_equality
    (heq : ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (ψ : Sentence language) (target : Sentenceᵢ language)
    (h : PRA ⊢ (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b)) 🡘 ∼ψ)
    (hcons : IPRANativeTheory.nativeTheory ⊢ (∼ψᴺ) 🡘 target) :
    IPRANativeTheory.nativeTheory ⊢
      (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![Semiterm.lMap embedding a, Semiterm.lMap embedding b]))) 🡘 target :=
  IPRAConditionalComparison.mapped_noZero_comparison_with_target
    (axiom_images_from_equality heq) n a b ψ target h hcons
theorem equality_images_from_remaining
    (hsymm : IPRANativeTheory.nativeTheory ⊢ (Theory.Eq.symm language)ᴺ)
    (htrans : IPRANativeTheory.nativeTheory ⊢ (Theory.Eq.trans language)ᴺ)
    (hfunc : ∀ {k : ℕ} (f : language.Func k),
      IPRANativeTheory.nativeTheory ⊢ (Theory.Eq.funcExt f)ᴺ)
    (hrel : ∀ {k : ℕ} (r : language.Rel k),
      IPRANativeTheory.nativeTheory ⊢ (Theory.Eq.relExt r)ᴺ) :
    ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ := by
  intro σ hσ
  cases hσ with
  | refl => exact IPRAEqualityImage.refl_image
  | symm => exact hsymm
  | trans => exact htrans
  | funcExt f => exact hfunc f
  | relExt r => exact hrel r
end DiophantineConsistency.IPRAEqualityRemaining
