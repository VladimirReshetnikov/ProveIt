import DiophantineConsistency.PRAStrictConComparison
import DiophantineConsistency.PRAConBForward
/-! The precise fixed-sentence witness-bound hypothesis needed to recover
Foundation's original negative sentence from its strict surrogate. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStrictConReverse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary StrictPiTwoBridge

def BoundCertificate (π : ArithmeticSentence) : Prop :=
  PRA ⊢ Semiformula.lMap embedding (π 🡒 ∃⁰ StrictSigmaOneInduction.bnd π)

/-- Only the bound certificate for this specific π is assumed. -/
theorem original_of_surrogate (π : ArithmeticSentence) (hbound : BoundCertificate π) :
    PRA ⊢ (Semiformula.lMap embedding (conB π) 🡒 Semiformula.lMap embedding (∼π)) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hb := models_of_provable hM hbound
  simp only [Semantics.Imp.models_imply] at ⊢
  intro hs
  simp only [models_iff] at hb hs ⊢
  rw [Semiformula.eval_lMap] at hb hs ⊢
  simp only [conB, Semiformula.eval_all, Semiformula.eval_ex,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] at hb hs ⊢
  intro hp
  obtain ⟨w,hw⟩ := hb hp
  exact hs w hw

/-- Full mapped equivalence follows if the fixed original refutation sentence
has its own actual candidate-PRA witness-bound proof. -/
theorem comparison_if_bound (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) (π : ArithmeticSentence)
    (hπ : Hierarchy 𝚺 1 π) (h : 𝗜𝚺₁ ⊢ (noZero n a b 🡘 ∼π))
    (hbound : BoundCertificate π) :
    PRA ⊢ (Semiformula.lMap embedding (noZero n a b) 🡘 Semiformula.lMap embedding (∼π)) := by
  have hstrict := PRAStrictConComparison.comparison n a b π hπ h
  have hf := PRAConBForward.PRA_proves_forward π
  have hb := original_of_surrogate π hbound
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hs := models_of_provable hM hstrict
  have hfm := models_of_provable hM hf
  have hbm := models_of_provable hM hb
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hs hfm hbm ⊢
  exact ⟨fun ha => hbm (hs.1 ha), fun hb' => hs.2 (hfm hb')⟩
end DiophantineConsistency.PRAStrictConReverse
