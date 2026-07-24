import BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSource

/-!
# Audit: fixed-source step for dynamic PA-axiom soundness

The declarations below expose the complete fixed source surface: the two
packed induction predicates, the generic closed induction axiom, the source
law context, the congruence-guarded step sentence, the semantic readings of
every new component, and the single lifted-PA derivation compiled by the
production layer.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSourceAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSource

#check sourceEquals
#check sourceAdd
#check sourceLevelAdjacency
#check sourceInductionAxiom
#check sourceFreeIndependenceAt
#check sourceFreeIndependencePredicate
#check sourceClosureAt
#check sourceClosurePredicate
#check sourceAxiomSoundnessLawContext
#check sourceAxiomSoundnessStepSentence
#check sourceCongruentAxiomSoundnessStepSentence
#check eval_sourceEquals
#check eval_sourceAdd
#check eval_sourceLevelAdjacency
#check eval_sourceInductionAxiom
#check eval_sourceFreeIndependenceAt
#check eval_sourceClosureAt
#check sourceCongruentAxiomSoundnessStepProof

#print axioms eval_sourceEquals
#print axioms eval_sourceAdd
#print axioms eval_sourceLevelAdjacency
#print axioms eval_sourceInductionAxiom
#print axioms eval_sourceFreeIndependenceAt
#print axioms eval_sourceClosureAt
#print axioms sourceCongruentAxiomSoundnessStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStrongStepSourceAudit
