import DiophantineConsistency.PRACurrentStrictCon
import DiophantineConsistency.PRAConBForward
/-! One literal direction only: Foundation ZFC consistency implies the
maintained equation has no positive solution. The converse remains open. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.PRACurrentConsistencyForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAConBForward FoundationHAConsistencyNormalization

theorem consistency_implies_noZero : PRA ⊢
    (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence 🡒
      Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence) := by
  simpa only [source_eq_neg_rho] using
    PRA_proves_literal_direction rho FoundationHACurrentNoZero2011.classicalSentence
      PRACurrentStrictCon.comparison
end DiophantineConsistency.PRACurrentConsistencyForward
