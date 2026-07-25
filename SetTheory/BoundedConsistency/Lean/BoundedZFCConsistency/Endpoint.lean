import BoundedZFCConsistency.AxiomTruth

/-!
# The endpoint: `ZFC |- Con_n(ZFC)` for every metatheoretic `n`

This module states the project's target in one place and audits it.  It adds no
mathematics; every ingredient is proved in the modules it imports.

The statement to read is `zfc_proves_conZFC`.  Three things about its shape are
the whole point of the project and are worth checking against the definitions
rather than taking on trust:

* `n` is an ordinary Lean `Nat`, so this is a *numeralwise family* — one
  separate object-level derivation for each metatheoretic `n`, produced by a
  metatheoretic function.  It is emphatically not a single derivation of a
  universally quantified sentence, which would yield ordinary `Con(ZFC)` and
  contradict Gödel's second incompleteness theorem.
* the conclusion is `TheorySyntacticConsequence ZFCax_s (conZFCForm n)`, which
  unfolds to `BProv ZFCax_s [] (conZFCForm n)`: a derivation in the repository's
  natural-deduction calculus from finitely many axioms of the sealed ZFC
  sentence theory.
* `conZFCForm n` quantifies over the derivation's *context* and constrains every
  member to be an internal ZFC axiom code, and bounds every formula occurrence
  of the derivation, not merely its conclusion.  An earlier attempt at this
  sentence used the empty context and so expressed bounded consistency of pure
  logic; the project README records that near miss.
-/

namespace LeanProofs
namespace BoundedZFCConsistency
namespace Endpoint

set_option autoImplicit false

open SetTheory
open SetTheory.FirstOrderClassicalCompleteness

/-- **The target.**  For every metatheoretic natural number `n`, the bounded
consistency statement `Con_n(ZFC)` is derivable from ZFC. -/
theorem zfc_proves_conZFC (n : Nat) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  zfcprov_conZFCForm n

/-- The same statement with the conclusion unfolded to the underlying
derivability predicate, so that no notation hides what is being claimed. -/
theorem zfc_proves_conZFC_unfolded (n : Nat) :
    BProv ZFCax_s [] (conZFCForm n) :=
  zfcprov_conZFCForm n

/-! ## Audit

The headline theorem must depend on nothing beyond Lean's three standard
classical axioms.  In particular no `sorry`, no `native_decide`, and no premise
of the development may survive: `LevelTwoValuedAt`, `LevelSoundnessAt` and
`AxiomCodesTrueAt` were all named obligations at various points and are all
discharged. -/

#check @zfc_proves_conZFC
#check @zfc_proves_conZFC_unfolded
#check @conZFCForm
#check @sentence_conZFCForm

#print axioms zfc_proves_conZFC
#print axioms zfc_proves_conZFC_unfolded
#print axioms sentence_conZFCForm

end Endpoint
end BoundedZFCConsistency
end LeanProofs
