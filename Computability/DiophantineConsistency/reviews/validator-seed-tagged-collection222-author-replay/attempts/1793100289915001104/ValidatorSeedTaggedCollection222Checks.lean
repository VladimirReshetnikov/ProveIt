import ZFCinPA.ValidatorSeedTaggedCollection222

set_option autoImplicit false
set_option Elab.async false
namespace LeanProofs.ZFCinPA.ValidatorSeedTaggedCollection222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedTaggedCollection222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- The conclusion retains both exact antecedents, including coinciding labels.
example (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 memTerm t a 🡒 ∃⁰ collectionBody θ a t := tagged_collection θ a t
example (t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 memTerm t t 🡒 ∃⁰ collectionBody (⊥ : Semiformula V ℒₛₑₜ 2) t t :=
  tagged_collection ⊥ t t
example (a t : Term V ℒₛₑₜ) :
    Source V ⊢ collectionConclusion (⊤ : Semiformula V ℒₛₑₜ 2) a t := tagged_collection ⊤ a t

-- Global support's input is deliberately not restricted by a.
example (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    collectionBody θ a t=
      (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
        ((∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
          memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
          ∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
            θ.subst ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0]))) ⋏
        (∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
          memTerm (Bootstrapping.Semiterm.bvar 0) a.bShift.bShift 🡒
          (∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
            θ.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1])) 🡒
          ∃⁰ (memTerm t.bShift.bShift.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
            (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) ⋏
              θ.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1])))))) := rfl

example (p : V) : Source V ⊢ emptyAt (Bootstrapping.Semiterm.fvar p) 🡒
    memTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar 0) 🡒
    ∃⁰ collectionBody
      (∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) 🡒
        eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.fvar p)))
      (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar p) := tagged_collection _ _ _
example (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    (collectionBody θ a t).shift.shift=collectionBody θ.shift.shift a.shift.shift t.shift.shift := by simp
example (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    (collectionBody θ a t).free=collectionAt θ.shift a.shift t.shift (Bootstrapping.Semiterm.fvar 0) :=
  collectionBody_free θ a t
example (θ : Semiformula V ℒₛₑₜ 2) (y x' x : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm x' x 🡒 θ.subst ![y,x'] 🡒 θ.subst ![y,x] := matrix_second_transport θ y x' x
example : 𝚺₁-Function₄[V] collectionMatrixCode via collectionMatrixGraph := inferInstance
example : 𝚺₁-Function₃[V] collectionBodyCode via collectionBodyGraph := inferInstance
example : 𝚺₁-Function₃[V] collectionConclusionCode via collectionConclusionGraph := inferInstance
example (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    Proof seedTheory (taggedCollectionProof θ a t).val (collectionConclusion θ a t).val :=
  taggedCollectionProof_isProof θ a t
example (θ : Semiformula V ℒₛₑₜ 2) (a t : Term V ℒₛₑₜ) :
    collectionConclusionCode θ.val a.val t.val=(collectionConclusion θ a t).val :=
  collectionConclusionCode_eq θ a t

#print axioms matrix_second_transport
#print axioms tagged_collection
#print axioms taggedCollectionProof_isProof
#print axioms collectionMatrix_shift
#print axioms collectionMatrix_subst
#print axioms collectionBody_free
#print axioms collectionConclusion_shift
#print axioms collectionMatrix_defined
#print axioms collectionBody_defined
#print axioms collectionConclusion_defined
#print axioms collectionMatrixCode_eq
#print axioms collectionBodyCode_eq
#print axioms collectionConclusionCode_eq
end LeanProofs.ZFCinPA.ValidatorSeedTaggedCollection222Checks
