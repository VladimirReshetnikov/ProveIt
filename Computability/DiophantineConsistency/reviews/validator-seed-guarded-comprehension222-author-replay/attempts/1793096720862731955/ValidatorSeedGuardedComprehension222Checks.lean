import ZFCinPA.ValidatorSeedGuardedComprehension222

set_option autoImplicit false
set_option Elab.async false

namespace LeanProofs.ZFCinPA.ValidatorSeedGuardedComprehension222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedGuardedComprehension222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (x : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ rawPairBody x x := raw_pair x x
example (t : Term V ℒₛₑₜ) : Source V ⊢ emptyAt t 🡒 ∃⁰ rawPairBody t t := raw_pair_of_empty t t t
example (θ : Semiformula V ℒₛₑₜ 1) (t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ guardedBody θ t t := guarded_comprehension θ t t
example (B t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼eqTerm B t 🡒 ∃⁰ twoRootBody (⊥ : Semiformula V ℒₛₑₜ 1) B t :=
  raw_two_root ⊥ B t
example (U t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ guardedBody (⊤ : Semiformula V ℒₛₑₜ 1) U t :=
  guarded_comprehension ⊤ U t

example (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    guardedBody θ U t=
      (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
        (∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
          (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
            (memTerm (Bootstrapping.Semiterm.bvar 0) U.bShift.bShift ⋏
              θ.subst ![Bootstrapping.Semiterm.bvar 0]))))) := rfl

example (p : V) : Source V ⊢ emptyAt (Bootstrapping.Semiterm.fvar p) 🡒
    ∃⁰ guardedBody
      (∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
        eqTerm (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar p)))
      (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar p) :=
  guarded_comprehension _ _ _

example (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    (guardedBody θ U t).shift.shift=guardedBody θ.shift.shift U.shift.shift t.shift.shift := by simp
example (θ : Semiformula V ℒₛₑₜ 1) (B t r z p : Term V ℒₛₑₜ) :
    (twoRootMatrix θ B t r).subst ![z,p]=
      ((eqTerm p r ⋏ eqTerm z B) ⋎ ((eqTerm p t ⋏ eqTerm z t) ⋎
        (singletonAt p z ⋏ (memTerm z B ⋏ θ.subst ![z])))) := twoRootMatrix_subst _ _ _ _ _ _

example : 𝚺₁-Function₄[V] rawPairMatrixCode via rawPairMatrixGraph := inferInstance
example : 𝚺₁-Function₂[V] rawPairBodyCode via rawPairBodyGraph := inferInstance
example : 𝚺₁-Function₄[V] twoRootMatrixCode via twoRootMatrixGraph := inferInstance
example : 𝚺₁-Function₃[V] twoRootBodyCode via twoRootBodyGraph := inferInstance
example : 𝚺₁-Function₃[V] guardedBodyCode via guardedBodyGraph := inferInstance

example (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    Proof seedTheory (guardedProof θ U t).val (emptyAt t 🡒 ∃⁰ guardedBody θ U t).val :=
  guardedProof_isProof θ U t
example (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    guardedBodyCode θ.val U.val t.val=(guardedBody θ U t).val := guardedBodyCode_eq θ U t

#print axioms raw_pair_of_empty
#print axioms raw_pair
#print axioms raw_two_root
#print axioms guarded_comprehension
#print axioms rawPairEmptyProof_isProof
#print axioms rawPairProof_isProof
#print axioms twoRootProof_isProof
#print axioms guardedProof_isProof
#print axioms rawPairMatrix_shift
#print axioms rawPairBody_free
#print axioms twoRootMatrix_subst
#print axioms guardedBody_free
#print axioms rawPairMatrix_defined
#print axioms rawPairBody_defined
#print axioms twoRootMatrix_defined
#print axioms twoRootBody_defined
#print axioms guardedBody_defined
#print axioms rawPairMatrixCode_eq
#print axioms rawPairBodyCode_eq
#print axioms twoRootMatrixCode_eq
#print axioms twoRootBodyCode_eq
#print axioms guardedBodyCode_eq
end LeanProofs.ZFCinPA.ValidatorSeedGuardedComprehension222Checks
