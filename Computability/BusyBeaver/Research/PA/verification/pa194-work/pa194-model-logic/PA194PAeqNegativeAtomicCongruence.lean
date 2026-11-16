import PA194PAeqAtomicCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AtomicCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint Entailment Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem negative_atomic_replace {a b s t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (hs : IsSemiterm language 1 s) (ht : IsSemiterm language 1 t)
    (hab : Provable ordinaryPAeq (equalityCode a b)) :
    Provable ordinaryPAeq (imp language
      (neg language (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t)))
      (neg language (equalityCode (termSubst language (b∷(0:V)) s) (termSubst language (b∷(0:V)) t)))) := by
  let va := (a∷(0:V))
  let vb := (b∷(0:V))
  have hva : IsSemitermVec language 1 0 va := by simp [va,ha]
  have hvb : IsSemitermVec language 1 0 vb := by simp [vb,hb]
  have hsa := hva.termSubst hs
  have hsb := hvb.termSubst hs
  have hta := hva.termSubst ht
  have htb := hvb.termSubst ht
  obtain ⟨d,hd⟩ := hab
  have hba : Provable ordinaryPAeq (equalityCode b a) := ⟨_,Symmetry.liftCode_valid ha hb hd⟩
  have hrev := atomic_replace hb ha hs ht hba
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let A : Formula V language := ⟨equalityCode (termSubst language va s) (termSubst language va t), equality_valid hsa hta⟩
  let B : Formula V language := ⟨equalityCode (termSubst language vb s) (termSubst language vb t), equality_valid hsb htb⟩
  have h : T ⊢ B 🡒 A := (TProvable.iff_provable).mpr (by simpa [A,B,va,vb,Semiformula.imp_def,imp] using hrev)
  have hh : T ⊢ ∼A 🡒 ∼B := contra! h
  have hraw := (TProvable.iff_provable).mp hh
  have hnn : neg language (neg language (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t))) =
      equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t) :=
    (equality_valid hsa hta).isUFormula.neg_neg
  simpa [T,A,B,va,vb,Semiformula.imp_def,Semiformula.val_neg,imp,hnn] using hraw
#print axioms negative_atomic_replace
end PA194PAeq.AtomicCongruence
