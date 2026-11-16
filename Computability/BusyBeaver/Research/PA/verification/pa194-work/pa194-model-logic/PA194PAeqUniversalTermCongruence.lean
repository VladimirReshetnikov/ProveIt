import PA194PAeqContextTermCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.UniversalTermCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
noncomputable def typedEq {n : Nat} (t u : Semiterm V language n) : Semiformula V language n :=
  ⟨equalityCode t.val u.val,equality_valid t.isSemiterm u.isSemiterm⟩
scoped infix:55 " ≐ₚ " => typedEq

@[simp] theorem typedEq_shift {n : Nat} (t u : Semiterm V language n) :
    (t ≐ₚ u).shift = t.shift ≐ₚ u.shift := by
  ext; exact equality_shift t.isSemiterm u.isSemiterm
@[simp] theorem typedEq_subst {n m : Nat} (t u : Semiterm V language n) (w : SemitermVec V language n m) :
    (t ≐ₚ u).subst w = (t.subst w ≐ₚ u.subst w) := by
  ext; exact equality_subst w.isSemitermVec t.isSemiterm u.isSemiterm

theorem universal (t : Semiterm V language 1) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    (ordinaryPAeq.internalize V) ⊢ ∀⁰ ∀⁰ (((Semiterm.bvar 1 : Semiterm V language 2) ≐ₚ Semiterm.bvar 0) 🡒
      (t.subst ![Semiterm.bvar 1] ≐ₚ t.subst ![Semiterm.bvar 0])) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  have hs : IsSemiterm language 1 t.shift.shift.val := by simpa using t.shift.shift.isSemiterm
  have h := ContextCongruence.term_implication
    (show IsSemiterm language 0 (^&(1:V)) from by simp)
    (show IsSemiterm language 0 (^&(0:V)) from by simp)
    hs
  have hTyped : T ⊢ ((Semiterm.fvar 1 : Term V language) ≐ₚ Semiterm.fvar 0) 🡒
      (t.shift.shift.subst ![Semiterm.fvar 1] ≐ₚ t.shift.shift.subst ![Semiterm.fvar 0]) := by
    apply (TProvable.iff_provable).mpr
    simpa [T,typedEq,Semiformula.imp_def,imp,SemitermVec.val_succ] using h
  change T ⊢ ∀⁰ ∀⁰ (((Semiterm.bvar 1 : Semiterm V language 2) ≐ₚ Semiterm.bvar 0) 🡒
      (t.subst ![Semiterm.bvar 1] ≐ₚ t.subst ![Semiterm.bvar 0]))
  apply TProof.all₂!
  simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs] using hTyped
#print axioms typedEq_shift
#print axioms typedEq_subst
#print axioms universal
end PA194PAeq.UniversalTermCongruence
