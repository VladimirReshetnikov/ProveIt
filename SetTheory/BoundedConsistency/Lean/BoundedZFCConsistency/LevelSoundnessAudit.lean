import BoundedZFCConsistency.LevelSoundness

/-!
# Kernel audit for fixed-level substitution and the soundness boundary

The substitution lemmas below are proved.  The three `Prop`-valued definitions
are *not* theorems and deliberately have no assumption listing: they are the
named obligations this module leaves open, and the audit exists partly to keep
that visible.  Only `noBoundedRefutation_of_levelSoundness` is a theorem about
them, and it consumes two of them as hypotheses.
-/

namespace LeanProofs
namespace BoundedZFCConsistency
namespace LevelSoundnessAudit

/-! ## Substitution at a fixed level -/

#check @sigmaTrue_renames
#check @piFalse_renames
#check @piTrue_renames
#check @sigmaTrue_renameV
#check @piFalse_renameV
#check @sigmaTrue_renameV_succMap
#check @piFalse_renameV_succMap
#check @sigmaTrue_renameV_instMap
#check @piFalse_renameV_instMap

#print axioms sigmaTrue_renames
#print axioms piFalse_renames
#print axioms piTrue_renames
#print axioms sigmaTrue_renameV_succMap
#print axioms piFalse_renameV_succMap
#print axioms sigmaTrue_renameV_instMap
#print axioms piFalse_renameV_instMap

/-! ## Supporting code inductions -/

#check @qfSubstOK_of_isQFCodeSem
#check @levelSubstOK_of_isFormCodeSem
#check @isQFCodeSem_of_renames
#check @sigmaBounded_renames_iff
#check @piBounded_renames_iff

#print axioms qfSubstOK_of_isQFCodeSem
#print axioms levelSubstOK_of_isFormCodeSem

/-! ## The open obligations, and the one theorem about them

`AxiomCodesTrueAt` is where the content of the ZFC axioms enters, and it ranges
over the internal axiom set, nonstandard schema instances included.
`LevelTwoValuedAt` follows from the level-collapse theorem, which
`BoundedZFCConsistency.UniverseTruthLevel` leaves open.  `LevelSoundnessAt` is
blocked on `LevelTwoValuedAt` at implication elimination. -/

#check @AxiomCodesTrueAt
#check @LevelTwoValuedAt
#check @LevelSoundnessAt
#check @NoBoundedRefutationAtLevel

#check @noBoundedRefutation_of_levelSoundness
#print axioms noBoundedRefutation_of_levelSoundness

end LevelSoundnessAudit
end BoundedZFCConsistency
end LeanProofs
