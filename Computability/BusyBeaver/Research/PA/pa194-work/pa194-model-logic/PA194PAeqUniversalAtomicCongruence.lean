import PA194PAeqContextEquality
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.UniversalAtomicCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic PA194PAeq.UniversalTermCongruence
open PA194PAeqTermBlueprint PA194PAeq.UniversalTermCongruence Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem positive (s t : Semiterm V language 1) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    (ordinaryPAeq.internalize V) ⊢ ∀⁰ ∀⁰ (((Semiterm.bvar 1 : Semiterm V language 2) ≐ₚ Semiterm.bvar 0) 🡒
      ((s.subst ![Semiterm.bvar 1] ≐ₚ t.subst ![Semiterm.bvar 1]) 🡒
       (s.subst ![Semiterm.bvar 0] ≐ₚ t.subst ![Semiterm.bvar 0]))) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  have hs : IsSemiterm language 1 s.shift.shift.val := by simpa using s.shift.shift.isSemiterm
  have ht : IsSemiterm language 1 t.shift.shift.val := by simpa using t.shift.shift.isSemiterm
  have h := ContextCongruence.atomic_implication
    (show IsSemiterm language 0 (^&(1:V)) from by simp)
    (show IsSemiterm language 0 (^&(0:V)) from by simp) hs ht
  have hTyped : T ⊢ ((Semiterm.fvar 1 : Term V language) ≐ₚ Semiterm.fvar 0) 🡒
      ((s.shift.shift.subst ![Semiterm.fvar 1] ≐ₚ t.shift.shift.subst ![Semiterm.fvar 1]) 🡒
       (s.shift.shift.subst ![Semiterm.fvar 0] ≐ₚ t.shift.shift.subst ![Semiterm.fvar 0])) := by
    apply (TProvable.iff_provable).mpr
    simpa [T,typedEq,Semiformula.imp_def,imp,SemitermVec.val_succ] using h
  change T ⊢ ∀⁰ ∀⁰ (((Semiterm.bvar 1 : Semiterm V language 2) ≐ₚ Semiterm.bvar 0) 🡒
      ((s.subst ![Semiterm.bvar 1] ≐ₚ t.subst ![Semiterm.bvar 1]) 🡒
       (s.subst ![Semiterm.bvar 0] ≐ₚ t.subst ![Semiterm.bvar 0])))
  apply TProof.all₂!
  simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs] using hTyped

theorem negative (s t : Semiterm V language 1) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    (ordinaryPAeq.internalize V) ⊢ ∀⁰ ∀⁰ (((Semiterm.bvar 1 : Semiterm V language 2) ≐ₚ Semiterm.bvar 0) 🡒
      ((∼(s.subst ![Semiterm.bvar 1] ≐ₚ t.subst ![Semiterm.bvar 1])) 🡒
       (∼(s.subst ![Semiterm.bvar 0] ≐ₚ t.subst ![Semiterm.bvar 0])))) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  have hs : IsSemiterm language 1 s.shift.shift.val := by simpa using s.shift.shift.isSemiterm
  have ht : IsSemiterm language 1 t.shift.shift.val := by simpa using t.shift.shift.isSemiterm
  have h := ContextCongruence.negative_atomic_implication
    (show IsSemiterm language 0 (^&(1:V)) from by simp)
    (show IsSemiterm language 0 (^&(0:V)) from by simp) hs ht
  have hTyped : T ⊢ ((Semiterm.fvar 1 : Term V language) ≐ₚ Semiterm.fvar 0) 🡒
      ((∼(s.shift.shift.subst ![Semiterm.fvar 1] ≐ₚ t.shift.shift.subst ![Semiterm.fvar 1])) 🡒
       (∼(s.shift.shift.subst ![Semiterm.fvar 0] ≐ₚ t.shift.shift.subst ![Semiterm.fvar 0]))) := by
    apply (TProvable.iff_provable).mpr
    have hs1 : IsSemiterm language 0 (s.shift.shift.subst ![(Semiterm.fvar 1 : Term V language)]).val := by
      simpa using (s.shift.shift.subst ![(Semiterm.fvar 1 : Term V language)]).isSemiterm
    have ht1 : IsSemiterm language 0 (t.shift.shift.subst ![(Semiterm.fvar 1 : Term V language)]).val := by
      simpa using (t.shift.shift.subst ![(Semiterm.fvar 1 : Term V language)]).isSemiterm
    have hnn := (equality_valid hs1 ht1).isUFormula.neg_neg
    simp [SemitermVec.val_succ] at hnn
    simpa [T,typedEq,Semiformula.imp_def,Semiformula.val_neg,imp,SemitermVec.val_succ,hnn] using h
  change T ⊢ ∀⁰ ∀⁰ (((Semiterm.bvar 1 : Semiterm V language 2) ≐ₚ Semiterm.bvar 0) 🡒
      ((∼(s.subst ![Semiterm.bvar 1] ≐ₚ t.subst ![Semiterm.bvar 1])) 🡒
       (∼(s.subst ![Semiterm.bvar 0] ≐ₚ t.subst ![Semiterm.bvar 0]))))
  apply TProof.all₂!
  simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs] using hTyped
#print axioms positive
#print axioms negative
end PA194PAeq.UniversalAtomicCongruence
