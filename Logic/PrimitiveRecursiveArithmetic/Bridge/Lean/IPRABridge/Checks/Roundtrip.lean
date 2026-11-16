import IPRABridge.FoundationNormalization

set_option autoImplicit false

namespace IPRABridge.Checks.Roundtrip

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency
open PRAFiniteFunctionCodes (Code)
open IPRAStandardTheory (standardTheory)

-- A positive-arity zero sits inside a composition in the recursion step.
private def recWithZero : Code 1 :=
  .prec (.zero 0) (.comp (.zero 1) (.cons (.proj 1) (.nil 2)))

private def quantifiedOrder : Sentenceᵢ PRALanguage.language :=
  ∀⁰ (∃⁰ (.rel Language.ORing.Rel.lt ![.bvar 0, .func recWithZero (fun _ => .bvar 1)]))

example : standardTheory ⊢ quantifiedOrder 🡘
    toStandardSentence (toConciseSentence quantifiedOrder) :=
  standardSentenceRoundtrip quantifiedOrder

example : (standardTheory ⊢ quantifiedOrder) ↔
    Prf PRAAx [] (toConciseSentence quantifiedOrder) :=
  standardProvable_iff quantifiedOrder

#print axioms standardSentenceRoundtrip
#print axioms standardProvable_iff

end IPRABridge.Checks.Roundtrip
