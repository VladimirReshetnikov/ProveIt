import DiophantineConsistency.PRAWitnessDerivation
import DiophantineConsistency.PRAWitnessBoundCertificate
import DiophantineConsistency.PRAStrictConReverse
import DiophantineConsistency.PRACurrentStrictCon
/-! # PRA proves: the current equation has no positive zero ↔ ZFC is consistent

`PRAStrictConReverse.comparison_if_bound` reduced the literal equivalence
between the maintained equation's unsolvability and Foundation's actual ZFC
consistency sentence to one input, the bound certificate for the refutation
sentence `rho = ZFC ⊢ ⊥`: in every candidate-PRA model, a true `rho` has a
witness for its bounded form `bnd rho`. `PRAWitnessDerivation.wb_provable_falsum`
gives that witness, through the witness-bound calculus for every layer of
`rho` (syntax, recursions, the ZFC axiom recognizer, derivations), so
`boundCertificate_rho` holds and the equivalence is a PRA theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.PRACurrentConsistencyEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus StrictSigmaOneInduction

/-- **The bound certificate for `ZFC ⊢ ⊥`.** -/
theorem boundCertificate_rho :
    PRAStrictConReverse.BoundCertificate FoundationHAConsistencyNormalization.rho := by
  apply PRAWitnessBoundCertificate.certificate_of_witness_bounds
  intro M _ _ _ _
  exact PRAWitnessDerivation.wb_provable_falsum (M := M)

open FoundationHANoZero FoundationHAConsistencyNormalization ObjectCurrentEquation2011 in
/-- **PRA proves that the maintained equation has no positive zero iff ZFC is
consistent**, for Foundation's actual ZFC consistency sentence. -/
theorem pra_current_iff_consistency : PRA ⊢
    (Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence 🡘
      Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence) := by
  have h : 𝗜𝚺₁ ⊢
      (PRANoZeroUnary.noZero 14
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2)) 🡘 ∼rho) := by
    simpa only [PRANoZeroUnary.noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
      source_eq_neg_rho] using HACurrentEquation2011.isigma1_proves_current_iff_consistency
  have hc := PRAStrictConReverse.comparison_if_bound 14
    (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
    (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))
    rho rho_sigma_one h boundCertificate_rho
  simpa only [PRANoZeroUnary.noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
    source_eq_neg_rho] using hc

end DiophantineConsistency.PRACurrentConsistencyEndpoint
