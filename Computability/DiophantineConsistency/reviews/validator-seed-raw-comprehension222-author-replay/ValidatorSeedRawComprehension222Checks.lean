import ZFCinPA.ValidatorSeedRawComprehension222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedRawComprehension222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    Proof seedTheory (rawAugProof θ a).val (∃⁰ rawAugBody θ a).val :=
  rawAugProof_isProof θ a

example (k a r : V) : V ⊧/![rawAugMatrixCode k a r,k,a,r] rawAugMatrixGraph.val := by simp
example (k a : V) : V ⊧/![rawAugBodyCode k a,k,a] rawAugBodyGraph.val := by simp

example (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ seedPairAt K a c 🡒 memTerm y c 🡒 memberClosure K c y :=
  full_member_closure K a c y

-- The subset is of the member y, not the seed root a or support input x.
example (K : Semiformula V ℒₛₑₜ 2) (c y : Term V ℒₛₑₜ) :
    memberClosure K c y =
      ∀⁰ (subsetTerm (Bootstrapping.Semiterm.bvar 0) y.bShift 🡒
        ∀⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] 🡒
          ∃⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 2] ⋏
            memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift.bShift.bShift))) := rfl

example (a : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ rawAugBody ⊥ a := raw_augmented ⊥ a
example (a : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ rawAugBody ⊤ a := raw_augmented ⊤ a

def nested (p : V) : Semiformula V ℒₛₑₜ 1 :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) ⋎
    eqTerm (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar p))

example (p : V) :
    (rawAugBody (nested p) (Bootstrapping.Semiterm.fvar 0)).free=
      rawAugAt (nested p).shift (Bootstrapping.Semiterm.fvar 0).shift (Bootstrapping.Semiterm.fvar 0) :=
  rawAugBody_free _ _

example (p : V) :
    rawAugMatrixCode (nested p).val (Bootstrapping.Semiterm.fvar 0 : Term V ℒₛₑₜ).val
      (Bootstrapping.Semiterm.fvar p : Term V ℒₛₑₜ).val =
    (rawAugMatrix (nested p) (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar p)).val :=
  rawAugMatrixCode_eq _ _ _

example (p : V) : Source V ⊢ ∃⁰ rawAugBody (nested p) (Bootstrapping.Semiterm.fvar p) :=
  raw_augmented _ _

example (θ : Semiformula V ℒₛₑₜ 1) (a r : Term V ℒₛₑₜ) :
    (rawAugMatrix θ a r).shift.shift=rawAugMatrix θ.shift.shift a.shift.shift r.shift.shift := by simp

end LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222Checks

#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.full_member_closure
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugMatrix_shift
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugBody_shift
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugBody_free
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugMatrix_subst
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.raw_augmented
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugProof_isProof
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugMatrix_defined
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugBody_defined
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugMatrixCode_eq
#print axioms LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222.rawAugBodyCode_eq
