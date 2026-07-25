import BoundedZFCConsistency.Basic
import BoundedZFCConsistency.Choice
import BoundedZFCConsistency.CodedDerivation
import BoundedZFCConsistency.Coding
import BoundedZFCConsistency.CodePredicate
import BoundedZFCConsistency.Consistency
import BoundedZFCConsistency.FormulaClosedSet
import BoundedZFCConsistency.InternalSat
import BoundedZFCConsistency.InternalSatTotality
import BoundedZFCConsistency.InternalSoundness
import BoundedZFCConsistency.OmegaRecursion

/-!
# Bounded-complexity consistency for ZFC

This facade exposes the metatheoretic layer of the project: a polarity-aware
syntactic measure of "at most `n` quantifier groups" on the repository's
first-order set-theoretic syntax, that same measure applied at *every*
judgement node of a derivation, the axiom set of ZFC, and the model-relative
consistency statements which follow.

The intended theorem — for every metatheoretic `n`, an object-level derivation
`ZFC |- Con_n(ZFC)` — is **not** proved here.  Reaching it requires arithmetized
syntax inside the object theory, internal satisfaction for set-sized
structures, formalized soundness, and the Levy reflection scheme.  The project
README states the plan and the outstanding obligations.

Two properties of the present layer are easy to misread, so both are stated
precisely here and proved in the modules:

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
