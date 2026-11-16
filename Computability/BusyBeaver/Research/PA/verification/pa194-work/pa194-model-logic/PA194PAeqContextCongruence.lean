import PA194PAeqTermCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.ContextCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint PA194PAeqModusPonens Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem context_mp (Γ : Sequent V language) {p q : V} (hp : IsSemiformula language 0 p)
    (hq : IsSemiformula language 0 q) (hi : Provable ordinaryPAeq (imp language p q))
    (hd : Derivable ordinaryPAeq (insert p Γ.val)) : Derivable ordinaryPAeq (insert q Γ.val) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula V language := ⟨p,hp⟩
  let Q : Formula V language := ⟨q,hq⟩
  have hi' : T ⊢ P 🡒 Q := (TProvable.iff_provable).mpr (by simpa [P,Q,Semiformula.imp_def,imp] using hi)
  let hdi : T ⊢!ᵈᵉʳ insert (P 🡒 Q) Γ := TDerivation.wk hi'.get (by intro x hx; simp at hx ⊢; tauto)
  let hdp : T ⊢!ᵈᵉʳ insert P Γ := Derivable.toTDerivation _ hd
  let out := paeqMPProof T Γ P Q hdi hdp
  have h := out.toDerivable
  simpa [T,P,Q,instΔ₁Theory] using h

theorem context_mp_both (Γ : Sequent V language) {p q : V} (hp : IsSemiformula language 0 p)
    (hq : IsSemiformula language 0 q) (hi : Derivable ordinaryPAeq (insert (imp language p q) Γ.val))
    (hd : Derivable ordinaryPAeq (insert p Γ.val)) : Derivable ordinaryPAeq (insert q Γ.val) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula V language := ⟨p,hp⟩
  let Q : Formula V language := ⟨q,hq⟩
  let hdi : T ⊢!ᵈᵉʳ insert (P 🡒 Q) Γ := Derivable.toTDerivation _ (by simpa [T,P,Q,Semiformula.imp_def,imp] using hi)
  let hdp : T ⊢!ᵈᵉʳ insert P Γ := Derivable.toTDerivation _ hd
  let out := paeqMPProof T Γ P Q hdi hdp
  have h := out.toDerivable
  simpa [T,P,Q,instΔ₁Theory] using h

theorem context_refl (Γ : Sequent V language) {t : V} (ht : IsSemiterm language 0 t) :
    Derivable ordinaryPAeq (insert (equalityCode t t) Γ.val) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula V language := ⟨equalityCode t t,equality_valid ht ht⟩
  have hp : T ⊢ P := (TProvable.iff_provable).mpr (TermCongruence.reflexive ht)
  let out : T ⊢!ᵈᵉʳ insert P Γ := TDerivation.wk hp.get (by intro x hx; simp at hx ⊢; tauto)
  have h := out.toDerivable
  simpa [T,P,instΔ₁Theory] using h
theorem succ_imp {t u : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) :
    Provable ordinaryPAeq (imp language (equalityCode t u)
      (equalityCode (SuccCongruence.succTerm t) (SuccCongruence.succTerm u))) := by
  refine ⟨SuccCongruence.atTermsCode t u, ?_⟩
  have h := SuccCongruence.atTermsCode_valid ht hu
  rw [SuccCongruence.body_subst ht hu] at h
  simpa [Theory.internalize] using h

theorem add_imp {t u v w : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w) :
    Provable ordinaryPAeq (imp language (equalityCode t u) (imp language (equalityCode v w)
      (equalityCode (AddCongruenceInternal.addTerm t v) (AddCongruenceInternal.addTerm u w)))) := by
  refine ⟨AddCongruenceInternal.atTermsCode t u v w, ?_⟩
  have h := AddCongruenceInternal.atTermsCode_valid ht hu hv hw
  rw [AddCongruenceInternal.body_subst ht hu hv hw] at h
  simpa [Theory.internalize] using h

theorem mul_imp {t u v w : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w) :
    Provable ordinaryPAeq (imp language (equalityCode t u) (imp language (equalityCode v w)
      (equalityCode (MulCongruenceInternal.mulTerm t v) (MulCongruenceInternal.mulTerm u w)))) := by
  refine ⟨MulCongruenceInternal.atTermsCode t u v w, ?_⟩
  have h := MulCongruenceInternal.atTermsCode_valid ht hu hv hw
  rw [MulCongruenceInternal.body_subst ht hu hv hw] at h
  simpa [Theory.internalize] using h

theorem context_succ (Γ : Sequent V language) {t u : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hd : Derivable ordinaryPAeq (insert (equalityCode t u) Γ.val)) :
    Derivable ordinaryPAeq (insert (equalityCode (SuccCongruence.succTerm t) (SuccCongruence.succTerm u)) Γ.val) := by
  have ht' : IsSemiterm language 0 (SuccCongruence.succTerm t) := by simp [SuccCongruence.succTerm,source_functions,ht]
  have hu' : IsSemiterm language 0 (SuccCongruence.succTerm u) := by simp [SuccCongruence.succTerm,source_functions,hu]
  exact context_mp Γ (equality_valid ht hu) (equality_valid ht' hu') (succ_imp ht hu) hd

theorem context_add (Γ : Sequent V language) {t u v w : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w)
    (hd : Derivable ordinaryPAeq (insert (equalityCode t u) Γ.val))
    (he : Derivable ordinaryPAeq (insert (equalityCode v w) Γ.val)) :
    Derivable ordinaryPAeq (insert (equalityCode (AddCongruenceInternal.addTerm t v) (AddCongruenceInternal.addTerm u w)) Γ.val) := by
  have htv : IsSemiterm language 0 (AddCongruenceInternal.addTerm t v) := by simp [AddCongruenceInternal.addTerm,source_functions,ht,hv]
  have huw : IsSemiterm language 0 (AddCongruenceInternal.addTerm u w) := by simp [AddCongruenceInternal.addTerm,source_functions,hu,hw]
  have hp := equality_valid ht hu
  have hq := equality_valid hv hw
  have hr := equality_valid htv huw
  have hi : IsSemiformula language 0 (imp language (equalityCode v w)
      (equalityCode (AddCongruenceInternal.addTerm t v) (AddCongruenceInternal.addTerm u w))) := IsSemiformula.imp.mpr ⟨hq,hr⟩
  have hfirst := context_mp Γ hp hi (add_imp ht hu hv hw) hd
  exact context_mp_both Γ hq hr hfirst he

theorem context_mul (Γ : Sequent V language) {t u v w : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w)
    (hd : Derivable ordinaryPAeq (insert (equalityCode t u) Γ.val))
    (he : Derivable ordinaryPAeq (insert (equalityCode v w) Γ.val)) :
    Derivable ordinaryPAeq (insert (equalityCode (MulCongruenceInternal.mulTerm t v) (MulCongruenceInternal.mulTerm u w)) Γ.val) := by
  have htv : IsSemiterm language 0 (MulCongruenceInternal.mulTerm t v) := by simp [MulCongruenceInternal.mulTerm,source_functions,ht,hv]
  have huw : IsSemiterm language 0 (MulCongruenceInternal.mulTerm u w) := by simp [MulCongruenceInternal.mulTerm,source_functions,hu,hw]
  have hp := equality_valid ht hu
  have hq := equality_valid hv hw
  have hr := equality_valid htv huw
  have hi : IsSemiformula language 0 (imp language (equalityCode v w)
      (equalityCode (MulCongruenceInternal.mulTerm t v) (MulCongruenceInternal.mulTerm u w))) := IsSemiformula.imp.mpr ⟨hq,hr⟩
  have hfirst := context_mp Γ hp hi (mul_imp ht hu hv hw) hd
  exact context_mp_both Γ hq hr hfirst he

#print axioms succ_imp
#print axioms add_imp
#print axioms mul_imp
#print axioms context_succ
#print axioms context_add
#print axioms context_mul
#print axioms context_mp
#print axioms context_refl
end PA194PAeq.ContextCongruence
