import PA194PAeqContextCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.ContextCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem term_replace (Γ : Sequent V language) {a b t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (ht : IsSemiterm language 1 t)
    (hab : Derivable ordinaryPAeq (insert (equalityCode a b) Γ.val)) :
    Derivable ordinaryPAeq (insert (equalityCode (termSubst language (a∷(0:V)) t) (termSubst language (b∷(0:V)) t)) Γ.val) := by
  have hva : IsSemitermVec language 1 0 (a∷(0:V)) := by simp [ha]
  have hvb : IsSemitermVec language 1 0 (b∷(0:V)) := by simp [hb]
  apply IsSemiterm.induction 𝚺 (P := fun t => Derivable ordinaryPAeq
    (insert (equalityCode (termSubst language (a∷(0:V)) t) (termSubst language (b∷(0:V)) t)) Γ.val)) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    have hz' : z = 0 := lt_one_iff_eq_zero.mp hz
    subst z
    simpa using hab
  · intro x
    simpa using context_refl Γ (show IsSemiterm language 0 (^&x) from by simp)
  · intro k f vs hf hvs ih
    rw [termSubst_func hf hvs.isUTerm, termSubst_func hf hvs.isUTerm]
    rcases (source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩
    · have hvz : vs = 0 := IsSemitermVec.empty_iff.mp hvs
      subst vs
      simpa using context_refl Γ (show IsSemiterm language 0 (^func (0:V) 0 0) from by simp [source_functions])
    · obtain ⟨s,rfl⟩ := eq_singleton_iff_len_eq_one.mp hvs.lh
      have hs : IsSemiterm language 1 s := by simpa using hvs.nth (i:=0) (by simp)
      have hd := ih 0 (by simp)
      have hd' : Derivable ordinaryPAeq (insert (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s)) Γ.val) := by simpa using hd
      have h := context_succ Γ (hva.termSubst hs) (hvb.termSubst hs) hd'
      simpa [termSubstVec_cons₁ hs.isUTerm,SuccCongruence.succTerm] using h
    · obtain ⟨s,r,rfl⟩ := eq_doubleton_of_len_eq_two.mp hvs.lh
      have hs : IsSemiterm language 1 s := by simpa using hvs.nth (i:=0) (by simp)
      have hr : IsSemiterm language 1 r := by simpa using hvs.nth (i:=1) (by simp)
      have hd := ih 0 (by simp)
      have he := ih 1 (by simp)
      have hd' : Derivable ordinaryPAeq (insert (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s)) Γ.val) := by simpa using hd
      have he' : Derivable ordinaryPAeq (insert (equalityCode (termSubst language (a∷(0:V)) r) (termSubst language (b∷(0:V)) r)) Γ.val) := by simpa using he
      have h := context_add Γ (hva.termSubst hs) (hvb.termSubst hs) (hva.termSubst hr) (hvb.termSubst hr) hd' he'
      simpa [termSubstVec_cons₂ hs.isUTerm hr.isUTerm,AddCongruenceInternal.addTerm] using h
    · obtain ⟨s,r,rfl⟩ := eq_doubleton_of_len_eq_two.mp hvs.lh
      have hs : IsSemiterm language 1 s := by simpa using hvs.nth (i:=0) (by simp)
      have hr : IsSemiterm language 1 r := by simpa using hvs.nth (i:=1) (by simp)
      have hd := ih 0 (by simp)
      have he := ih 1 (by simp)
      have hd' : Derivable ordinaryPAeq (insert (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s)) Γ.val) := by simpa using hd
      have he' : Derivable ordinaryPAeq (insert (equalityCode (termSubst language (a∷(0:V)) r) (termSubst language (b∷(0:V)) r)) Γ.val) := by simpa using he
      have h := context_mul Γ (hva.termSubst hs) (hvb.termSubst hs) (hva.termSubst hr) (hvb.termSubst hr) hd' he'
      simpa [termSubstVec_cons₂ hs.isUTerm hr.isUTerm,MulCongruenceInternal.mulTerm] using h
theorem term_implication {a b t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (ht : IsSemiterm language 1 t) :
    Provable ordinaryPAeq (imp language (equalityCode a b)
      (equalityCode (termSubst language (a∷(0:V)) t) (termSubst language (b∷(0:V)) t))) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula V language := ⟨equalityCode a b,equality_valid ha hb⟩
  have hva : IsSemitermVec language 1 0 (a∷(0:V)) := by simp [ha]
  have hvb : IsSemitermVec language 1 0 (b∷(0:V)) := by simp [hb]
  let Q : Formula V language := ⟨equalityCode (termSubst language (a∷(0:V)) t) (termSubst language (b∷(0:V)) t),
    equality_valid (hva.termSubst ht) (hvb.termSubst ht)⟩
  let Γ : Sequent V language := {∼P}
  let seed : T ⊢!ᵈᵉʳ insert P Γ := TDerivation.em P (by simp) (by simp [Γ])
  have hseed : Derivable ordinaryPAeq (insert (equalityCode a b) Γ.val) := by
    simpa [T,P,instΔ₁Theory] using seed.toDerivable
  have h := term_replace Γ ha hb ht hseed
  let d : T ⊢!ᵈᵉʳ insert Q Γ := Derivable.toTDerivation _ (by simpa [T,Q,instΔ₁Theory] using h)
  have d' : T ⊢!ᵈᵉʳ insert (∼P) (insert Q ∅) := TDerivation.wk d (by intro x hx; simp [Γ] at hx ⊢; tauto)
  have out : T ⊢! (P 🡒 Q) := by
    change T ⊢!ᵈᵉʳ insert (P 🡒 Q) ∅
    have e := TDerivation.or d'
    simpa [Semiformula.imp_def] using e
  refine ⟨out.val, ?_⟩
  simpa [T,P,Q,Proof,instΔ₁Theory,Semiformula.imp_def,imp,← singleton_eq_insert] using out.derivationOf

#print axioms term_implication
#print axioms term_replace
end PA194PAeq.ContextCongruence
