import IPRABridge.Standard
import IPRABridge.ReferenceNormalization

/-! Reflection of closed Foundation derivability across the Concise translation. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment LeanProofs.ConciseIPRA
open scoped LO.FirstOrder IPRABridge
open DiophantineConsistency
open IPRAOrderErasure (embed erase)
open IPRAStandardTheory (standardTheory)

/-- The Foundation sentence obtained by a round trip through ConciseIPRA
is provably equivalent to the original sentence in standard iPRA. -/
theorem standardSentenceRoundtrip (φ : Sentenceᵢ PRALanguage.language) :
    standardTheory ⊢ φ 🡘 toStandardSentence (toConciseSentence φ) := by
  have h : standardTheory ⊢ embed (erase φ) 🡘 embed (normalizeFormula (erase φ)) :=
    referenceToStandard (referenceNormalization (erase φ))
  have hscope : (Fin.elim0 : Fin 0 → PTm 0) = PTm.var := funext (fun i => Fin.elim0 i)
  simp only [toStandardSentence, toConciseSentence, toConciseClosed, hscope, referenceFormula_roundtrip]
  exact Entailment.E!_trans (standardOrderRoundtrip φ) h

/-- Standard Foundation iPRA proves a closed sentence exactly when ConciseIPRA
proves its translation. -/
theorem standardProvable_iff (φ : Sentenceᵢ PRALanguage.language) :
    (standardTheory ⊢ φ) ↔ Prf PRAAx [] (toConciseSentence φ) := by
  refine ⟨standardToConcise, fun h => ?_⟩
  exact ⟨Entailment.K_right (standardSentenceRoundtrip φ).some ⨀ (conciseToStandard h).some⟩

end IPRABridge
