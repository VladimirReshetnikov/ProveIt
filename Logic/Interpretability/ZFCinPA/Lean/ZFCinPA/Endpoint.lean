import ZFCinPA.StandardSuccessor

/-!
# The endpoint: `PA ⊢ ∀ n, Prov_ZFC(⌜Conₙ(ZFC)⌝)`, and its exact residue

This module states the project's target in one place, together with the
*complete* chain that now leads to it, and audits both.  It adds no
mathematics: every ingredient is proved in the modules it imports.

## The chain

```
ZFCSuccessorImplicationsInAllModels          (six flat internal implications)
  → ZFCStagedSuccessorInAllModels            (StagedSuccessor)
  → ZFCProofSelectorInAllModels              (BaseCertificate / StagedCompiler)
  → Peano ⊢ paUniformZFCProvabilitySentence  (UniformStatement, completeness)
```

Everything below the first arrow is proved.  The first arrow is proved
here as well: `ZFCinPA.StagedSuccessor` reduces the staged successor —
four `UniversalKernel`s at four cumulative contexts plus two direct
implications — to six flat implications out of one and the same
antecedent.

## The residue

What is *not* proved is either hypothesis at the top of the chain.  Both
are stated below as named `Prop`s so that no reader has to reconstruct
them:

* `ZFCStagedSuccessorInAllModels` — the literal `HasStagedSuccessor` of
  `ZFCinPA.StagedCompiler` for the concrete family, in every model of PA;
* `ZFCSuccessorImplicationsInAllModels` — its flat form: at every model
  index `n`, internal `𝗭𝗙𝗖` proofs that the level-`n` master certificate
  implies each of the five level-`(n+1)` truth laws and the internalized
  `Con_{n+1}(ZFC)`.

`zfcStagedSuccessorInAllModels_iff_successorImplications` proves the two
equivalent, so the flattening is a reformulation and not a weakening.

`ZFCinPA.StandardSuccessor` discharges the second one at every *standard*
index, by goal 2's semantics plus D1.  The residue is therefore exactly
the nonstandard indices of a nonstandard model — where the level-`n`
certificate has to be genuinely consumed, and where no metatheoretic
family of derivations can help.

## Reading the audit

The `#print axioms` lines below must show only Lean's three standard
classical axioms.  A conditional theorem is honest only if its hypothesis
is really used, so the audit also `#check`s the two hypothesis `Prop`s and
the endpoint's own type: `set_option autoImplicit false` is in force
throughout the project precisely so that an out-of-scope identifier in a
statement cannot silently become an implicit variable and make a
verification vacuous.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA
namespace Endpoint

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## The two forms of the remaining obligation -/

/-- **The remaining obligation, staged form.**  The literal
`HasStagedSuccessor` of `ZFCinPA.StagedCompiler`, for the concrete
certificate family of `ZFCinPA.ConcreteFamily`, in every model of PA. -/
def ZFCStagedSuccessorInAllModels : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    HasStagedSuccessor (concreteZFCTruthCertificateFamily (V := V))

/-- **The remaining obligation, flat form.**  Six internal `𝗭𝗙𝗖`
implications out of the level-`n` master certificate, at every index of
every model of PA. -/
def ZFCSuccessorImplicationsInAllModels : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)),
    Nonempty (ZFCSuccessorImplications n h)

/-- The flat form implies the staged form. -/
theorem zfcStagedSuccessorInAllModels_of_successorImplications
    (H : ZFCSuccessorImplicationsInAllModels) :
    ZFCStagedSuccessorInAllModels := by
  intro V _ _ _
  exact hasStagedSuccessor_of_nonempty_successorImplications (H V)

/-- The staged form implies the flat form: flattening the staircase of
cumulative contexts loses nothing. -/
theorem zfcSuccessorImplicationsInAllModels_of_stagedSuccessor
    (H : ZFCStagedSuccessorInAllModels) :
    ZFCSuccessorImplicationsInAllModels := by
  intro V _ _ _ n h
  exact hasStagedSuccessor_iff_successorImplications.mp (H V) n h

/-- **The two forms of the remaining obligation are the same
obligation.** -/
theorem zfcStagedSuccessorInAllModels_iff_successorImplications :
    ZFCStagedSuccessorInAllModels ↔ ZFCSuccessorImplicationsInAllModels :=
  ⟨zfcSuccessorImplicationsInAllModels_of_stagedSuccessor,
    zfcStagedSuccessorInAllModels_of_successorImplications⟩

/-! ## The chain to the selector and to PA -/

/-- The staged successor gives the model-internal proof selector in every
model of PA. -/
theorem zfcProofSelectorInAllModels_of_stagedSuccessor
    (H : ZFCStagedSuccessorInAllModels) :
    ZFCProofSelectorInAllModels := by
  intro V _ _ _
  exact zfcProofSelectorIn_of_concreteStagedSuccessor (H V)

/-- **The target, from the staged successor.**  Peano Arithmetic derives
the literal sentence "for every `n`, `ZFC` proves `Conₙ(ZFC)`". -/
theorem peano_proves_uniformZFCProvability_of_stagedSuccessor
    (H : ZFCStagedSuccessorInAllModels) :
    Peano ⊢ paUniformZFCProvabilitySentence :=
  peano_proves_uniformZFCProvability_of_selectorInAllModels
    (zfcProofSelectorInAllModels_of_stagedSuccessor H)

/-- **The target, from the six flat implications.**  This is the complete
current reduction of the project. -/
theorem peano_proves_uniformZFCProvability_of_successorImplications
    (H : ZFCSuccessorImplicationsInAllModels) :
    Peano ⊢ paUniformZFCProvabilitySentence :=
  peano_proves_uniformZFCProvability_of_stagedSuccessor
    (zfcStagedSuccessorInAllModels_of_successorImplications H)

/-- The same conclusion with the sentence's semantic reading spelled out,
so that no notation hides what is being claimed: the derived sentence says
that in every model, every element `x` — standard or not — has a `𝗭𝗙𝗖`-provable
consistency code. -/
theorem peano_proves_uniformZFCProvability_of_successorImplications_unfolded
    (H : ZFCSuccessorImplicationsInAllModels)
    (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ∀ x : V, Provable 𝗭𝗙𝗖 (conZFCSetCodeFun x) :=
  eval_paUniformZFCProvabilitySentence_iff_fun.mp
    (eval_paUniformZFCProvabilitySentence_iff_selector.mpr
      (zfcProofSelectorInAllModels_of_stagedSuccessor
        (zfcStagedSuccessorInAllModels_of_successorImplications H) V))

/-! ## Audit

The endpoint is conditional: its hypothesis is one of the two named
obligations above, and nothing else.  The `#check` lines make the exact
shapes of those obligations, and of the conclusion, visible; the
`#print axioms` lines confirm that no `sorry`, no `native_decide`, and no
project-specific axiom entered the chain. -/

#check @ZFCStagedSuccessorInAllModels
#check @ZFCSuccessorImplicationsInAllModels
#check @ZFCSuccessorImplications
#check @HasStagedSuccessor
#check @ZFCProofSelectorInAllModels
#check @paUniformZFCProvabilitySentence

#check @zfcStagedSuccessorInAllModels_of_successorImplications
#check @zfcSuccessorImplicationsInAllModels_of_stagedSuccessor
#check @zfcStagedSuccessorInAllModels_iff_successorImplications
#check @zfcProofSelectorInAllModels_of_stagedSuccessor
#check @peano_proves_uniformZFCProvability_of_stagedSuccessor
#check @peano_proves_uniformZFCProvability_of_successorImplications
#check @peano_proves_uniformZFCProvability_of_successorImplications_unfolded

#print axioms zfcStagedSuccessorInAllModels_of_successorImplications
#print axioms zfcSuccessorImplicationsInAllModels_of_stagedSuccessor
#print axioms zfcStagedSuccessorInAllModels_iff_successorImplications
#print axioms zfcProofSelectorInAllModels_of_stagedSuccessor
#print axioms peano_proves_uniformZFCProvability_of_stagedSuccessor
#print axioms peano_proves_uniformZFCProvability_of_successorImplications
#print axioms peano_proves_uniformZFCProvability_of_successorImplications_unfolded

end Endpoint
end ZFCinPA
end LeanProofs
