import BoundedPAConsistency.DynamicTruthBaseMasterCertificate
import BoundedPAConsistency.DynamicTruthStagedSuccessorAssembly

/-!
# The uniform internal provability theorem

Every ingredient of the staged direct package is now available for the
concrete dynamic truth family:

* its six-field master code has a Sigma-one graph;
* index zero carries a genuine typed PA derivation of that master
  certificate;
* every index carries a dependency-ordered successor step whose public target
  is the family's next master certificate.

Sigma-one induction inside an arbitrary ambient PA model therefore produces a
proof code for the master certificate at *every* model element, including the
nonstandard ones, and the forced sixth coordinate turns each such code into a
proof code for the corresponding restricted-consistency instance.  That is
exactly the model-internal selector, so arithmetic completeness returns the
object theorem

```
PA ⊢ ∀ n, ∃ p, ssnum(p, ⌜Con_·(PA)⌝, n) ∧ Prov_PA(p),
```

with the level quantifier at the object level.  No induction on external
natural numbers appears anywhere in the chain, which is what distinguishes
this statement from the schema `PA ⊢ Con_n(PA)` for each standard `n`.
-/

namespace LeanProofs.BoundedPAConsistency.UniformInternalProvabilityTheorem

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthBaseMasterCertificate
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateFieldFamily
open LeanProofs.BoundedPAConsistency.DynamicTruthStagedSuccessorAssembly
open LeanProofs.BoundedPAConsistency.StagedDirectTruthCertificatePackage
open LeanProofs.BoundedPAConsistency.UniformInternalProvability

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The model-internal restricted-consistency proof selector, constructed in
an arbitrary model of PA from the compiled dynamic truth certificates.

The selector is genuinely internal: for a nonstandard `n` it returns a
nonstandard element of `V` that the represented proof predicate accepts as a
PA derivation of the `n`-th bounded consistency statement. -/
theorem paRestrictedConsistencyProofSelectorIn_compiled :
    PARestrictedConsistencyProofSelectorIn V :=
  paRestrictedConsistencyProofSelectorIn_of_stagedDirectTypedTruthCertificates
    (compiledDynamicTruthCertificateFamily (V := V))
    compiledDynamicTruthCertificateFamily_code_definable
    compiledDynamicTruthBaseCertificateProof
    compiledDynamicTruthCertificateFamily_hasStagedSuccessor

/-- The same construction runs in every model of PA. -/
theorem paRestrictedConsistencyProofSelectorInAllModels_compiled :
    PARestrictedConsistencyProofSelectorInAllModels := by
  intro M _ _ _
  exact paRestrictedConsistencyProofSelectorIn_compiled

/-- PA proves that every bounded consistency statement about PA is provable
in PA, with the level quantifier inside the object language.

This is the unconditional endpoint of the development.  The three trust
boundaries of an ordinary Lean proof—propositional extensionality, choice,
and quotient soundness—are the only assumptions; there is no additional
axiom, no `native_decide`, and no reflection principle. -/
theorem pa_proves_uniformRestrictedConsistencyProvability :
    Peano ⊢ paUniformRestrictedConsistencyProvabilitySentence :=
  pa_proves_uniformRestrictedConsistencyProvability_of_selectorInAllModels
    paRestrictedConsistencyProofSelectorInAllModels_compiled

end LeanProofs.BoundedPAConsistency.UniformInternalProvabilityTheorem
