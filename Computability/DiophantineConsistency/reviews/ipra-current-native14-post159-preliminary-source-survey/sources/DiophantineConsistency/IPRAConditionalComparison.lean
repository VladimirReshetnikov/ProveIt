import DiophantineConsistency.IntuitionisticPRABridge
import DiophantineConsistency.IPRAIffGG
import DiophantineConsistency.IPRANativeTheory
import DiophantineConsistency.IPRAMappedNoZero
/-! Conditional assembly: all PRA axiom images and consistency-side
identification remain explicit hypotheses. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAConditionalComparison
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory

theorem translated_comparison
    (hax : ∀ σ ∈ PRA, IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (φ ψ : Sentence language) (h : PRA ⊢ φ 🡘 ∼ψ) :
    IPRANativeTheory.nativeTheory ⊢ φᴺ 🡘 ∼ψᴺ :=
  IPRAIffGG.unpack_iff_neg_image IPRANativeTheory.nativeTheory φ ψ
    (IntuitionisticPRABridge.from_classical IPRANativeTheory.nativeTheory hax h)

theorem comparison_with_target
    (hax : ∀ σ ∈ PRA, IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (φ ψ : Sentence language) (target : Sentenceᵢ language)
    (h : PRA ⊢ φ 🡘 ∼ψ)
    (hcons : IPRANativeTheory.nativeTheory ⊢ (∼ψᴺ) 🡘 target) :
    IPRANativeTheory.nativeTheory ⊢ φᴺ 🡘 target :=
  Entailment.E!_trans (translated_comparison hax φ ψ h) hcons
theorem mapped_noZero_comparison_with_target
    (hax : ∀ σ ∈ PRA, IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (ψ : Sentence language) (target : Sentenceᵢ language)
    (h : PRA ⊢ (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b)) 🡘 ∼ψ)
    (hcons : IPRANativeTheory.nativeTheory ⊢ (∼ψᴺ) 🡘 target) :
    IPRANativeTheory.nativeTheory ⊢
      (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![Semiterm.lMap embedding a, Semiterm.lMap embedding b]))) 🡘 target := by
  simpa only [IPRAMappedNoZero.mapped_gg_noZero] using
    comparison_with_target hax (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b)) ψ target h hcons
end DiophantineConsistency.IPRAConditionalComparison
