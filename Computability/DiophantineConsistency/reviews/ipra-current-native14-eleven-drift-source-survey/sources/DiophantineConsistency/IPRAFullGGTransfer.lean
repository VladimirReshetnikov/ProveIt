import DiophantineConsistency.IPRAEqualityRemaining
import DiophantineConsistency.IPRAEqualitySymmetryGG
import DiophantineConsistency.IPRAEqualityTransGG
import DiophantineConsistency.IPRABinaryRelationGG
import DiophantineConsistency.IPRAFunctionCongruenceGG
/-! Gödel–Gentzen translation of classical candidate PRA into the separately
specified native intuitionistic PR-code theory. The identification of the
translated consistency predicate with a chosen native one is separate. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAFullGGTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory

theorem equality_images : ∀ σ ∈ (𝗘𝗤 language), nativeTheory ⊢ σᴺ :=
  IPRAEqualityRemaining.equality_images_from_remaining
    IPRAEqualitySymmetryGG.symmetry_image IPRAEqualityTransGG.trans_image
    IPRAFunctionCongruenceGG.funcExt_image IPRABinaryRelationGG.relExt_image

theorem axiom_images : ∀ σ ∈ PRA, nativeTheory ⊢ σᴺ :=
  IPRAEqualityRemaining.axiom_images_from_equality equality_images

theorem from_classical {φ : Sentence language} (h : PRA ⊢ φ) : nativeTheory ⊢ φᴺ :=
  IntuitionisticPRABridge.from_classical nativeTheory axiom_images h

theorem mapped_noZero_comparison
    (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (ψ : Sentence language) (target : Sentenceᵢ language)
    (h : PRA ⊢ (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b)) 🡘 ∼ψ)
    (hcons : nativeTheory ⊢ (∼ψᴺ) 🡘 target) :
    nativeTheory ⊢
      (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![Semiterm.lMap embedding a, Semiterm.lMap embedding b]))) 🡘 target :=
  IPRAEqualityRemaining.mapped_noZero_from_equality equality_images n a b ψ target h hcons
end DiophantineConsistency.IPRAFullGGTransfer
