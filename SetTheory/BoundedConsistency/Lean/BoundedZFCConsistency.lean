import BoundedZFCConsistency.AxiomCode
import BoundedZFCConsistency.AxiomTruth
import BoundedZFCConsistency.Basic
import BoundedZFCConsistency.Endpoint
import BoundedZFCConsistency.Choice
import BoundedZFCConsistency.CodedDerivation
import BoundedZFCConsistency.CodedRank
import BoundedZFCConsistency.Coding
import BoundedZFCConsistency.CodePredicate
import BoundedZFCConsistency.Consistency
import BoundedZFCConsistency.FormulaClosedSet
import BoundedZFCConsistency.InternalSat
import BoundedZFCConsistency.InternalSatTotality
import BoundedZFCConsistency.InternalSoundness
import BoundedZFCConsistency.LevelCollapse
import BoundedZFCConsistency.LevelSoundness
import BoundedZFCConsistency.LevelSoundnessProof
import BoundedZFCConsistency.OmegaRecursion
import BoundedZFCConsistency.UniverseTruthLevel
import BoundedZFCConsistency.UniverseTruthZero

/-!
# Bounded-complexity consistency for ZFC

This facade exposes the metatheoretic layer of the project: a polarity-aware
syntactic measure of "at most `n` quantifier groups" on the repository's
first-order set-theoretic syntax, that same measure applied at *every*
judgement node of a derivation, the axiom set of ZFC, and the model-relative
consistency statements which follow.

The intended theorem is proved.  For every metatheoretic `n`,
`Endpoint.zfc_proves_conZFC` derives `Con_n(ZFC)` from ZFC.  The route runs
through coded syntax inside the object theory, internal satisfaction, coded
derivations with their soundness, and an externally indexed partial truth
hierarchy over the universe — not through Levy reflection, which the project
README explains was abandoned as the more expensive of the two options.

Two properties of the metatheoretic layer are easy to misread, so both are
stated precisely here and proved in the modules:

* The rank counts *every* quantifier, because this syntax has no primitive
  bounded quantifier.  It is therefore strictly finer than the Levy hierarchy,
  and each `Con_n` built on it is correspondingly weaker.  What the intended
  theorem actually needs — that the restricted relations exhaust all derivations
  as `n` grows — is unaffected, and is proved as cofinality.
* No consistency statement here is unconditional.  Each carries a model of the
  axiom set as an explicit hypothesis.  That is not because consistency of ZFC
  is unavailable in Lean, whose type theory is stronger than ZFC and does prove
  it, but because no bridge yet connects such a model to this syntax.
-/
