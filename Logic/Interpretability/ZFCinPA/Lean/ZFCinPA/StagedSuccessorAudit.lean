import ZFCinPA.StagedSuccessor

/-!
# Audit for the staged-successor reduction

The audit keeps the module's layers visible in their types:

* the generic peeling of one coded universal quantifier, and the four
  peeled kernel predicates of the concrete family with the equations
  identifying their universal closures with the fields themselves;
* the five context weakenings and the kernel installer;
* the six-implication record, the staged step built from it, and the two
  target identifications;
* the reduction of `HasStagedSuccessor` — and hence of the model-internal
  proof selector — to those six implications.
-/

namespace LeanProofs.ZFCinPA.StagedSuccessorAudit

open LeanProofs.ZFCinPA

/-! ## Peeling -/

#check @peelAll
#check @peelAll_val
#check @all_peelAll

/-! ## The peeled bodies and predicates -/

#check @crossLevelBodyPart
#check @shiftInvariantBodyPart
#check @substitutionInvariantBodyPart
#check @axiomSoundBodyPart
#check @crossLevelFormula_val_eq_all
#check @shiftInvariantFormula_val_eq_all
#check @substitutionInvariantFormula_val_eq_all
#check @axiomSoundFormula_val_eq_all
#check @crossLevelPredicate
#check @shiftInvariantPredicate
#check @substitutionInvariantPredicate
#check @axiomSoundPredicate
#check @all_crossLevelPredicate
#check @all_shiftInvariantPredicate
#check @all_substitutionInvariantPredicate
#check @all_axiomSoundPredicate

/-! ## Contexts and the kernel installer -/

#check @localContext_imp
#check @crossContext_imp
#check @shiftContext_imp
#check @substitutionContext_imp
#check @soundnessContext_imp
#check @kernelOfImplication
#check @kernelOfImplication_predicate

/-! ## The six implications and the staged step -/

#check @ZFCSuccessorImplications
#check @stagedStepOfImplications
#check @stagedStepOfImplications_target
#check @stagedStepOfImplications_target_val

/-! ## The reduction -/

#check @hasStagedSuccessor_of_successorImplications
#check @hasStagedSuccessor_of_nonempty_successorImplications
#check @zfcProofSelectorIn_of_successorImplications

/-! ## The converse, and the exactness of the reduction -/

#check @stagedStep_target_sentence_val
#check @concreteFamily_code_eq
#check @successorImplicationsOfStagedStep
#check @hasStagedSuccessor_iff_successorImplications

/-! ## Assumption audit

The reduction is proof-theoretic plumbing over Foundation's classical
internal calculus, so `Classical.choice`, `propext` and `Quot.sound` are
expected; nothing beyond Lean's three standard axioms should appear, and
in particular no `sorry` and no theory-specific axiom. -/

#print axioms all_peelAll
#print axioms all_crossLevelPredicate
#print axioms all_shiftInvariantPredicate
#print axioms all_substitutionInvariantPredicate
#print axioms all_axiomSoundPredicate
#print axioms stagedStepOfImplications_target
#print axioms stagedStepOfImplications_target_val
#print axioms hasStagedSuccessor_of_successorImplications
#print axioms hasStagedSuccessor_of_nonempty_successorImplications
#print axioms zfcProofSelectorIn_of_successorImplications
#print axioms successorImplicationsOfStagedStep
#print axioms tarskiElimContext_imp
#print axioms tarskiIntroContext_imp
#print axioms hasStagedSuccessor_iff_successorImplications

end LeanProofs.ZFCinPA.StagedSuccessorAudit
