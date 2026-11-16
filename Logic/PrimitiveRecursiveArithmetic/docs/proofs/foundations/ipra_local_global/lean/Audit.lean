import ObjectExample
import NegativeSyntax
import ODETargets
import SplitTargets

#print axioms LeanProofs.ConciseIPRA.LocalGlobal.qf_subst
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.primitiveRecursionInvariant
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.primitiveRecursionAt
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.counting_is_time
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.negative_subst
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.negative_qf
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.negative_inductionFormula
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.translatedInductionAxiom
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.translatedExcludedMiddle
#print axioms LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.negative_classical_axiom

-- These are types only. #check is NOT evidence that a Goal is proved.
#check LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax.ProofTranslationGoal
#check IPRALocalGlobal.ODE.LocalExistenceGoal
#check IPRALocalGlobal.ODE.ConservationGoal
#check IPRALocalGlobal.Split.splitXBoundGoal
#check IPRALocalGlobal.Split.enumerateSolutionsIffGoal
