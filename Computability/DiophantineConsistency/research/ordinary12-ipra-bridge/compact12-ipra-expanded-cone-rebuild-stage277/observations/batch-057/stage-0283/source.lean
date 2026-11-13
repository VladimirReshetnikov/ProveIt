import ZFCinPA.UniversalKernel
import ZFCinPA.CertificateFamily

/-!
# Staged compilation of `𝗭𝗙𝗖` truth certificates

This is the `ℒₛₑₜ` mirror of the arithmetic
`BoundedPAConsistency.StagedTruthCertificateProofCompiler` together with its
direct-package plumbing (`StagedDirectTruthCertificatePackage`).  The eight
laws of a truth certificate are not logically independent: a concrete
construction first proves the local clauses, uses them while proving
cross-level coherence, then uses the accumulated laws for substitution and
axiom soundness, and finally derives the internalized consistency conclusion
from everything established at the new level.  The context therefore grows
after every stage:

```
previous + local + cross-level + shift + substitution + axiom soundness
  -> final consistency.
```

The four recursive fields are `UniversalKernel`s — where the arithmetic
compiler ran PA's model-coded induction axiom, the set-theoretic kernels are
expected to arrive from `UniversalKernel.ofOmegaInduction` (internalized
ω-induction via Separation plus Infinity) or from structural universal
proofs, but the compiler itself only consumes their compiled implications.

The endpoint `zfcProofSelectorIn_of_stagedCertificates` feeds the compiled
successor codes to `ZFCinPA.PackageInduction`'s direct master-proof
induction: the package witness is the actual proof code of the eight-field
master certificate, the master-code function is the `𝚺₁`-definable
`ZFCTruthCertificateFamily.code`, and final extraction is the forced eighth
field.  The remaining obligations of the whole uniform-provability project
are thereby exactly: one concrete `ZFCTruthCertificateFamily` with `𝚺₁`
field-code graphs, a base certificate at level `0`, and a staged successor
step at every (possibly nonstandard) model index.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Cumulative contexts -/

/-- Context after the direct local law has been proved. -/
noncomputable def localContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField : Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  previous.sentence ⋏ localField

/-- Context after the cross-level kernel has compiled. -/
noncomputable def crossContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross : Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  localContext previous localField ⋏ cross

/-- Context after the shift-invariance kernel has compiled. -/
noncomputable def shiftContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift : Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  crossContext previous localField cross ⋏ shift

/-- Context after the substitution-invariance kernel has compiled. -/
noncomputable def substitutionContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift substitution : Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  shiftContext previous localField cross shift ⋏ substitution

/-- Context after axiom soundness, immediately before the Tarski
elimination clauses. -/
noncomputable def soundnessContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift substitution axiomSound :
      Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  substitutionContext previous localField cross shift substitution ⋏
    axiomSound

/-- Context after the Tarski elimination clauses have been proved. -/
noncomputable def tarskiElimContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift substitution axiomSound tarskiElim :
      Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  soundnessContext previous localField cross shift substitution axiomSound ⋏
    tarskiElim

/-- Complete context, immediately before final consistency. -/
noncomputable def tarskiIntroContext
    (previous : ZFCTruthCertificateFields (V := V))
    (localField cross shift substitution axiomSound tarskiElim tarskiIntro :
      Bootstrapping.Formula V ℒₛₑₜ) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  tarskiElimContext previous localField cross shift substitution axiomSound
      tarskiElim ⋏
    tarskiIntro

/-! ## A dependency-aware successor step -/

/-- One successor certificate whose proof obligations are compiled in their
mathematical dependency order.

The four recursive fields are `UniversalKernel`s whose contexts name exactly
the fields available at that point.  The final direct proof sees the full
new soundness context, so it can invoke the newly proved truth and axiom
laws when excluding a restricted derivation of falsity. -/
structure ZFCStagedCertificateStep
    (T : InternalTheory V ℒₛₑₜ)
    (previous : ZFCTruthCertificateFields (V := V)) where
  localStep : Bootstrapping.Formula V ℒₛₑₜ
  proveLocalStep : T ⊢! previous.sentence 🡒 localStep

  crossLevel : UniversalKernel T (localContext previous localStep)

  shiftInvariant : UniversalKernel T
    (crossContext previous localStep (∀⁰ crossLevel.predicate))

  substitutionInvariant : UniversalKernel T
    (shiftContext previous localStep (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate))

  axiomSound : UniversalKernel T
    (substitutionContext previous localStep
      (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate)
      (∀⁰ substitutionInvariant.predicate))

  tarskiElim : Bootstrapping.Formula V ℒₛₑₜ
  proveTarskiElim : T ⊢!
    soundnessContext previous localStep
      (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate)
      (∀⁰ substitutionInvariant.predicate)
      (∀⁰ axiomSound.predicate) 🡒 tarskiElim

  tarskiIntro : Bootstrapping.Formula V ℒₛₑₜ
  proveTarskiIntro : T ⊢!
    tarskiElimContext previous localStep
      (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate)
      (∀⁰ substitutionInvariant.predicate)
      (∀⁰ axiomSound.predicate) tarskiElim 🡒 tarskiIntro

  finalConsistency : Bootstrapping.Formula V ℒₛₑₜ
  proveFinalConsistency : T ⊢!
    tarskiIntroContext previous localStep
      (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate)
      (∀⁰ substitutionInvariant.predicate)
      (∀⁰ axiomSound.predicate) tarskiElim tarskiIntro 🡒 finalConsistency

namespace ZFCStagedCertificateStep

variable {T : InternalTheory V ℒₛₑₜ}

/-- The public eight fields produced by a staged successor step. -/
noncomputable def target
    {previous : ZFCTruthCertificateFields (V := V)}
    (step : ZFCStagedCertificateStep T previous) :
    ZFCTruthCertificateFields (V := V) where
  localStep := step.localStep
  crossLevel := ∀⁰ step.crossLevel.predicate
  shiftInvariant := ∀⁰ step.shiftInvariant.predicate
  substitutionInvariant := ∀⁰ step.substitutionInvariant.predicate
  axiomSound := ∀⁰ step.axiomSound.predicate
  tarskiElim := step.tarskiElim
  tarskiIntro := step.tarskiIntro
  finalConsistency := step.finalConsistency

/-- Compile all eight stages into one typed proof of the successor master
certificate.

The intermediate conjunctions are retained only as proof objects used to
feed the next kernel.  The returned formula is `target.sentence`, exactly
the right-associated public certificate consumed by the package layer. -/
noncomputable def compile
    {previous : ZFCTruthCertificateFields (V := V)}
    (step : ZFCStagedCertificateStep T previous)
    (hprevious : T ⊢! previous.sentence) :
    T ⊢! step.target.sentence := by
  let hlocal : T ⊢! step.localStep :=
    TProof.modusPonens step.proveLocalStep hprevious
  let hlocalContext : T ⊢! localContext previous step.localStep :=
    Entailment.K_intro hprevious hlocal
  let hcross : T ⊢! ∀⁰ step.crossLevel.predicate :=
    step.crossLevel.compile hlocalContext
  let hcrossContext : T ⊢!
      crossContext previous step.localStep
        (∀⁰ step.crossLevel.predicate) :=
    Entailment.K_intro hlocalContext hcross
  let hshift : T ⊢! ∀⁰ step.shiftInvariant.predicate :=
    step.shiftInvariant.compile hcrossContext
  let hshiftContext : T ⊢!
      shiftContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate) :=
    Entailment.K_intro hcrossContext hshift
  let hsubstitution : T ⊢! ∀⁰ step.substitutionInvariant.predicate :=
    step.substitutionInvariant.compile hshiftContext
  let hsubstitutionContext : T ⊢!
      substitutionContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate)
        (∀⁰ step.substitutionInvariant.predicate) :=
    Entailment.K_intro hshiftContext hsubstitution
  let haxiom : T ⊢! ∀⁰ step.axiomSound.predicate :=
    step.axiomSound.compile hsubstitutionContext
  let hsoundness : T ⊢!
      soundnessContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate)
        (∀⁰ step.substitutionInvariant.predicate)
        (∀⁰ step.axiomSound.predicate) :=
    Entailment.K_intro hsubstitutionContext haxiom
  let helim : T ⊢! step.tarskiElim :=
    TProof.modusPonens step.proveTarskiElim hsoundness
  let helimContext : T ⊢!
      tarskiElimContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate)
        (∀⁰ step.substitutionInvariant.predicate)
        (∀⁰ step.axiomSound.predicate) step.tarskiElim :=
    Entailment.K_intro hsoundness helim
  let hintro : T ⊢! step.tarskiIntro :=
    TProof.modusPonens step.proveTarskiIntro helimContext
  let hintroContext : T ⊢!
      tarskiIntroContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate)
        (∀⁰ step.substitutionInvariant.predicate)
        (∀⁰ step.axiomSound.predicate) step.tarskiElim step.tarskiIntro :=
    Entailment.K_intro helimContext hintro
  let hfinal : T ⊢! step.finalConsistency :=
    TProof.modusPonens step.proveFinalConsistency hintroContext
  exact step.target.intro hlocal hcross hshift hsubstitution haxiom helim
    hintro hfinal

/-- The staged compiler's value is recognized by the internalized proof
predicate of the underlying theory. -/
lemma compile_isProof
    {previous : ZFCTruthCertificateFields (V := V)}
    (step : ZFCStagedCertificateStep T previous)
    (hprevious : T ⊢! previous.sentence) :
    Proof T.theory (step.compile hprevious).val
      step.target.sentence.val := by
  simpa [Proof] using (step.compile hprevious).derivationOf

set_option backward.isDefEq.respectTransparency false in
/-- The same bridge with the public `𝗭𝗙𝗖` theory instance used by the
package relation.  The transparency option only identifies the public
`ZFC_delta1` instance with the same instance stored by `Theory.internalize`;
it does not choose or alter the generated proof code. -/
lemma compile_isZFCProof
    {previous : ZFCTruthCertificateFields (V := V)}
    (step : ZFCStagedCertificateStep
      ((𝗭𝗙𝗖 : SetTheory).internalize V) previous)
    (hprevious : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! previous.sentence) :
    Proof 𝗭𝗙𝗖 (step.compile hprevious).val
      step.target.sentence.val := by
  simpa [Proof] using (step.compile hprevious).derivationOf

end ZFCStagedCertificateStep

/-! ## Staged successor witnesses for a certificate family -/

/-- A dependency-aware staged successor at every model index.

The equality is intentionally on raw public sentence codes: intermediate
cumulative contexts are private to the staged compiler, and identifying the
compiled target with the next family member at the code level avoids ever
forcing definitional equality of large represented formulas.  The
well-formedness witness is quantified so that the statement can name
`family.fields n h`; consumers recover it from the incoming master proof. -/
def HasStagedSuccessor
    (family : ZFCTruthCertificateFamily (V := V)) : Prop :=
  ∀ (n : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)),
    ∃ step : ZFCStagedCertificateStep
        ((𝗭𝗙𝗖 : SetTheory).internalize V) (family.fields n h),
      step.target.sentence.val = family.code (n + 1)

/-- One staged successor witness extends any incoming master proof: the
witness is the actual value of the typed staged compilation, its `𝗭𝗙𝗖` proof
judgment comes from `compile_isZFCProof`, and the supplied target-code
equality changes only the conclusion code to the next family member. -/
lemma exists_zfcMasterProof_succ_of_staged
    (family : ZFCTruthCertificateFamily (V := V))
    (successorTemplates : HasStagedSuccessor family)
    {n d : V}
    (hd : Proof 𝗭𝗙𝗖 d (family.code n)) :
    ∃ d' : V, Proof 𝗭𝗙𝗖 d' (family.code (n + 1)) := by
  have hcon : IsFormula ℒₛₑₜ (conZFCSetCodeFun n) :=
    family.isFormula_conCode_of_masterProof hd
  rcases successorTemplates n hcon with ⟨step, htarget⟩
  let previous : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      (family.fields n hcon).sentence :=
    family.toTProof hcon hd
  let next := step.compile previous
  refine ⟨next.val, ?_⟩
  have hproof : Proof 𝗭𝗙𝗖 next.val step.target.sentence.val :=
    step.compile_isZFCProof previous
  rw [← htarget]
  exact hproof

/-! ## The staged selector endpoints -/

/-- A `𝚺₁` master code, a base master proof, and staged successor witnesses
give the model-internal proof selector.

The induction is `PackageInduction`'s `𝚺₁` direct master-proof induction
inside the ambient model; this theorem contributes only the successor
witness construction above, and final extraction is the forced eighth
certificate field. -/
theorem zfcProofSelectorIn_of_stagedCertificates
    (family : ZFCTruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate : ∃ d : V, Proof 𝗭𝗙𝗖 d (family.code 0))
    (successorTemplates : HasStagedSuccessor family) :
    ZFCProofSelectorIn V := by
  apply zfcProofSelectorIn_of_directMasterProofs
    (masterCode := family.code) masterCodeDefinable
  · exact baseCertificate
  · intro x d hd
    exact exists_zfcMasterProof_succ_of_staged
      family successorTemplates hd
  · intro x d hd
    exact family.exists_finalProof_of_masterProof hd

set_option backward.isDefEq.respectTransparency false in
/-- Typed-base form of the staged selector.  Concrete constructions
normally assemble their level-zero certificate with
`ZFCTruthCertificateFields.intro`, so this form avoids a manual conversion
to the raw proof predicate; the base well-formedness witness is the
standard-point fact `isFormula_conZFCSetCodeFun_zero`.  (The transparency
option again only unfolds the `internalize` wrapper's `Δ₁` instance.) -/
theorem zfcProofSelectorIn_of_stagedTypedCertificates
    (family : ZFCTruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      (family.fields 0 isFormula_conZFCSetCodeFun_zero).sentence)
    (successorTemplates : HasStagedSuccessor family) :
    ZFCProofSelectorIn V := by
  apply zfcProofSelectorIn_of_stagedCertificates
    family masterCodeDefinable
  · exact ⟨baseCertificate.val, by
      simpa [Proof] using baseCertificate.derivationOf⟩
  · exact successorTemplates

/-- Public staged endpoint for a concrete dynamic truth family.

The seven premises represent exactly the variable field-code functions; the
eighth field's graph is `conZFCSetCodeGraph`, discharged by
`CertificateFamily`.  Together with the typed base certificate and staged
successor witnesses this is the complete remaining interface of the uniform
internal-provability project. -/
theorem zfcProofSelectorIn_of_stagedCertificates_and_fieldCodes
    (family : ZFCTruthCertificateFamily (V := V))
    (localStepDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.localStep n).val))
    (crossLevelDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.crossLevel n).val))
    (shiftInvariantDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.shiftInvariant n).val))
    (substitutionInvariantDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.substitutionInvariant n).val))
    (axiomSoundDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.axiomSound n).val))
    (tarskiElimDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.tarskiElim n).val))
    (tarskiIntroDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ (family.tarskiIntro n).val))
    (baseCertificate : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      (family.fields 0 isFormula_conZFCSetCodeFun_zero).sentence)
    (successorTemplates : HasStagedSuccessor family) :
    ZFCProofSelectorIn V := by
  apply zfcProofSelectorIn_of_stagedTypedCertificates family
    (family.code_definable_of_fields
      localStepDefinable crossLevelDefinable shiftInvariantDefinable
      substitutionInvariantDefinable axiomSoundDefinable
      tarskiElimDefinable tarskiIntroDefinable)
    baseCertificate successorTemplates

end ZFCinPA
end LeanProofs
