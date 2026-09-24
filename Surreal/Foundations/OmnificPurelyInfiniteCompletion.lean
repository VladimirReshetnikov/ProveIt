import Surreal.Foundations.OmnificPurelyInfiniteIdeal
import Surreal.Algebra.IdempotentAdicCompletion

/-!
# Completion at the purely infinite ideal

The completion clause of `odg:cor:Pglobal` (also `odg:cor:Jglobal`). Since
all positive powers of the purely infinite ideal equal that ideal, its
adic completion is the ordinary discrete integer ring. The canonical map
is exactly integer constant extraction.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The adic completion of the actual omnific ring at its purely infinite ideal. -/
abbrev OmnificPurelyInfiniteCompletion :=
  AdicCompletion omnificPurelyInfiniteIdeal.{u} OmnificInteger.{u}

/-- Completion at the purely infinite ideal gives exactly the ordinary integer ring. -/
def omnificPurelyInfiniteCompletionEquiv : OmnificPurelyInfiniteCompletion.{u} ≃+* ℤ :=
  (AdicCompletionTopology.idempotentEquiv omnificPurelyInfiniteIdeal
    omnificPurelyInfiniteIdeal_idempotent).trans omnificQuotientEquiv

/-- The completion map is integer constant extraction. -/
@[simp] theorem omnificPurelyInfiniteCompletionEquiv_of (x : OmnificInteger.{u}) :
    omnificPurelyInfiniteCompletionEquiv
      (AdicCompletion.of omnificPurelyInfiniteIdeal OmnificInteger x) = omnificConstantCoeff x := by
  rw [omnificPurelyInfiniteCompletionEquiv, RingEquiv.trans_apply,
    AdicCompletionTopology.idempotentEquiv_of]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk omnificConstantCoeff_surjective x

local instance quotientTopology : TopologicalSpace (OmnificInteger.{u} ⧸
    omnificPurelyInfiniteIdeal) := ⊥
local instance quotientDiscrete : DiscreteTopology (OmnificInteger.{u} ⧸
    omnificPurelyInfiniteIdeal) := ⟨rfl⟩

private def integerQuotientHomeomorph : OmnificInteger.{u} ⧸ omnificPurelyInfiniteIdeal ≃ₜ ℤ where
  toEquiv := omnificQuotientEquiv.toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The ideal-adic completion is homeomorphic to the usual discrete integer ring. -/
def omnificPurelyInfiniteCompletionHomeomorph : OmnificPurelyInfiniteCompletion.{u} ≃ₜ ℤ :=
  (AdicCompletionTopology.idempotentHomeomorph omnificPurelyInfiniteIdeal
    omnificPurelyInfiniteIdeal_idempotent).trans integerQuotientHomeomorph

/-- The completion homeomorphism has exactly the underlying ring equivalence as its function. -/
@[simp] theorem omnificPurelyInfiniteCompletionHomeomorph_apply
    (x : OmnificPurelyInfiniteCompletion.{u}) :
    omnificPurelyInfiniteCompletionHomeomorph x = omnificPurelyInfiniteCompletionEquiv x := rfl

/-- The topological completion identification preserves constant extraction as well. -/
@[simp] theorem omnificPurelyInfiniteCompletionHomeomorph_of (x : OmnificInteger.{u}) :
    omnificPurelyInfiniteCompletionHomeomorph
      (AdicCompletion.of omnificPurelyInfiniteIdeal OmnificInteger x) = omnificConstantCoeff x :=
  omnificPurelyInfiniteCompletionEquiv_of x

end
end Surreal.Foundations.SignSequence
