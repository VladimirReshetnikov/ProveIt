import ZFCinPA.ValidatorSeedTransitive222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedTransitive222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedRawComprehension222
open ValidatorSeedTransitive222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ rawTransitiveBody a := raw_transitive a
example (a t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t := tagged_transitive a t
example (x y t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ taggedPairBody x y t := tagged_pair x y t

-- Repeated markers/coordinates remain literal, without a distinctness hypothesis.
example (t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 memTerm t t 🡒 ∃⁰ taggedTransitiveBody t t := tagged_transitive t t
example (x t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ taggedPairBody x x t := tagged_pair x x t
example (y t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ taggedPairBody t y t := tagged_pair t y t
example (k l : V) : Source V ⊢ emptyAt (Bootstrapping.Semiterm.fvar l) 🡒
    ∃⁰ taggedPairBody (Bootstrapping.Semiterm.fvar (k+37))
      (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar l) := tagged_pair _ _ _

example (v p : Term V ℒₛₑₜ) :
    (transitiveMatrix (V := V)).subst ![v,p]=singletonAt p v := transitiveMatrix_subst v p
example : transitiveMatrix (V := V)=∀⁰
    (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) 🡘
      eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) := by
  simp [transitiveMatrix,singTerm,memTerm,eqTerm]
example (a : Term V ℒₛₑₜ) : rawTransitiveBody a=
    memTerm a.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
      (∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
        ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
          memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2)))) := by
  simp [rawTransitiveBody,transitiveTerm,subsetTerm,memTerm]
example (a t : Term V ℒₛₑₜ) :
    (taggedTransitiveBody a t).free=taggedTransitiveAt a.shift t.shift
      (Bootstrapping.Semiterm.fvar 0) := taggedTransitiveBody_free a t
example (x y t : Term V ℒₛₑₜ) :
    (taggedPairBody x y t).shift=taggedPairBody x.shift y.shift t.shift := taggedPairBody_shift x y t

example (a : Term V ℒₛₑₜ) :
    Proof seedTheory (rawTransitiveProof a).val (∃⁰ rawTransitiveBody a).val := rawTransitiveProof_isProof a
example (a t : Term V ℒₛₑₜ) :
    Proof seedTheory (taggedTransitiveProof a t).val
      (emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t).val := taggedTransitiveProof_isProof a t
example (x y t : Term V ℒₛₑₜ) :
    Proof seedTheory (taggedPairProof x y t).val
      (emptyAt t 🡒 ∃⁰ taggedPairBody x y t).val := taggedPairProof_isProof x y t
example (a t : Term V ℒₛₑₜ) :
    taggedTransitiveBodyCode a.val t.val=(taggedTransitiveBody a t).val := taggedTransitiveBodyCode_eq a t

#print axioms transitiveMatrix_subst
#print axioms transitiveMatrix_quote
#print axioms transitiveMatrixCode_eq
#print axioms raw_transitive
#print axioms tagged_transitive
#print axioms tagged_pair
#print axioms rawTransitiveProof_isProof
#print axioms taggedTransitiveProof_isProof
#print axioms taggedPairProof_isProof
#print axioms rawTransitiveBodyCode_eq
#print axioms taggedTransitiveBodyCode_eq
#print axioms taggedPairBodyCode_eq
#print axioms rawTransitiveBody_defined
#print axioms taggedTransitiveBody_defined
#print axioms taggedPairBody_defined
#print axioms taggedTransitiveBody_free
#print axioms taggedPairBody_shift
end LeanProofs.ZFCinPA.ValidatorSeedTransitive222Checks
