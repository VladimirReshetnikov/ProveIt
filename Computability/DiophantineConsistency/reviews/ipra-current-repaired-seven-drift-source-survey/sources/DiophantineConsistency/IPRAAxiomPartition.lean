import DiophantineConsistency.IPRAInductionNativeGG
import DiophantineConsistency.IPRAConditionalComparison
/-! Induction is discharged; the equality, defining, and basic axiom-image
classes and the consistency identification remain explicit assumptions. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAAxiomPartition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory

theorem axiom_images_from_remaining
    (heq : ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (hdef : ∀ σ ∈ DefiningEquation, IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (hbasic : ∀ σ ∈ BasicAxiom, IPRANativeTheory.nativeTheory ⊢ σᴺ) :
    ∀ σ ∈ PRA, IPRANativeTheory.nativeTheory ⊢ σᴺ := by
  intro σ hσ
  change σ ∈ ((𝗘𝗤 language ∪ DefiningEquation ∪ InductionScheme language Semiformula.Open) ∪ BasicAxiom) at hσ
  rcases hσ with (hcore | hbasicσ)
  · rcases hcore with (heqdef | hind)
    · rcases heqdef with (heqσ | hdefσ)
      · exact heq σ heqσ
      · exact hdef σ hdefσ
    · exact IPRAInductionNativeGG.induction_scheme_gg σ hind
  · exact hbasic σ hbasicσ
theorem mapped_noZero_comparison_from_remaining
    (heq : ∀ σ ∈ (𝗘𝗤 language), IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (hdef : ∀ σ ∈ DefiningEquation, IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (hbasic : ∀ σ ∈ BasicAxiom, IPRANativeTheory.nativeTheory ⊢ σᴺ)
    (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (ψ : Sentence language) (target : Sentenceᵢ language)
    (h : PRA ⊢ (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b)) 🡘 ∼ψ)
    (hcons : IPRANativeTheory.nativeTheory ⊢ (∼ψᴺ) 🡘 target) :
    IPRANativeTheory.nativeTheory ⊢
      (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![Semiterm.lMap embedding a, Semiterm.lMap embedding b]))) 🡘 target :=
  IPRAConditionalComparison.mapped_noZero_comparison_with_target
    (axiom_images_from_remaining heq hdef hbasic) n a b ψ target h hcons
end DiophantineConsistency.IPRAAxiomPartition
