import PA194PAeqAddCongruenceLift
import PA194PAeqMulCongruenceLift
import PA194PAeqSuccCongruenceExact
import PA194PAeqReflexivityExact
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.TermCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem reflexive {t : V} (ht : IsSemiterm language 0 t) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    Provable ordinaryPAeq (equalityCode t t) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  refine ⟨Reflexivity.atTermCode t, ?_⟩
  have h := Reflexivity.atTermCode_exact ht
  simpa [Theory.internalize] using h

theorem replace {a b t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (ht : IsSemiterm language 1 t)
    (hab : Provable ordinaryPAeq (equalityCode a b)) :
    Provable ordinaryPAeq (equalityCode (termSubst language (a∷(0:V)) t) (termSubst language (b∷(0:V)) t)) := by
  have hva : IsSemitermVec language 1 0 (a∷(0:V)) := by simp [ha]
  have hvb : IsSemitermVec language 1 0 (b∷(0:V)) := by simp [hb]
  apply IsSemiterm.induction 𝚺 (P := fun t => Provable ordinaryPAeq
    (equalityCode (termSubst language (a∷(0:V)) t) (termSubst language (b∷(0:V)) t))) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    have hz' : z = 0 := lt_one_iff_eq_zero.mp hz
    subst z
    simpa using hab
  · intro x
    simpa using reflexive (show IsSemiterm language 0 (^&x) from by simp)
  · intro k f vs hf hvs ih
    rw [termSubst_func hf hvs.isUTerm, termSubst_func hf hvs.isUTerm]
    rcases (source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩
    · have hvz : vs = 0 := IsSemitermVec.empty_iff.mp hvs
      subst vs
      simpa using reflexive (show IsSemiterm language 0 (^func (0:V) 0 0) from by simp [source_functions])
    · obtain ⟨s,rfl⟩ := eq_singleton_iff_len_eq_one.mp hvs.lh
      have hs : IsSemiterm language 1 s := by simpa using hvs.nth (i:=0) (by simp)
      obtain ⟨d,hd⟩ := ih 0 (by simp)
      have hd' : Proof ordinaryPAeq d (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s)) := by simpa using hd
      have hsa := hva.termSubst hs
      have hsb := hvb.termSubst hs
      refine ⟨SuccCongruence.liftCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s) d, ?_⟩
      have h := SuccCongruence.liftCode_valid hsa hsb hd'
      simpa [termSubstVec_cons₁ hs.isUTerm,SuccCongruence.succTerm] using h
    · obtain ⟨s,r,rfl⟩ := eq_doubleton_of_len_eq_two.mp hvs.lh
      have hs : IsSemiterm language 1 s := by simpa using hvs.nth (i:=0) (by simp)
      have hr : IsSemiterm language 1 r := by simpa using hvs.nth (i:=1) (by simp)
      obtain ⟨d,hd⟩ := ih 0 (by simp)
      obtain ⟨e,he⟩ := ih 1 (by simp)
      have hd' : Proof ordinaryPAeq d (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s)) := by simpa using hd
      have he' : Proof ordinaryPAeq e (equalityCode (termSubst language (a∷(0:V)) r) (termSubst language (b∷(0:V)) r)) := by simpa using he
      have hsa := hva.termSubst hs
      have hsb := hvb.termSubst hs
      have hra := hva.termSubst hr
      have hrb := hvb.termSubst hr
      refine ⟨AddCongruenceInternal.liftCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s) (termSubst language (a∷(0:V)) r) (termSubst language (b∷(0:V)) r) d e, ?_⟩
      have h := AddCongruenceInternal.liftCode_valid hsa hsb hra hrb hd' he'
      simpa [termSubstVec_cons₂ hs.isUTerm hr.isUTerm,AddCongruenceInternal.addTerm] using h
    · obtain ⟨s,r,rfl⟩ := eq_doubleton_of_len_eq_two.mp hvs.lh
      have hs : IsSemiterm language 1 s := by simpa using hvs.nth (i:=0) (by simp)
      have hr : IsSemiterm language 1 r := by simpa using hvs.nth (i:=1) (by simp)
      obtain ⟨d,hd⟩ := ih 0 (by simp)
      obtain ⟨e,he⟩ := ih 1 (by simp)
      have hd' : Proof ordinaryPAeq d (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s)) := by simpa using hd
      have he' : Proof ordinaryPAeq e (equalityCode (termSubst language (a∷(0:V)) r) (termSubst language (b∷(0:V)) r)) := by simpa using he
      have hsa := hva.termSubst hs
      have hsb := hvb.termSubst hs
      have hra := hva.termSubst hr
      have hrb := hvb.termSubst hr
      refine ⟨MulCongruenceInternal.liftCode (termSubst language (a∷(0:V)) s) (termSubst language (b∷(0:V)) s) (termSubst language (a∷(0:V)) r) (termSubst language (b∷(0:V)) r) d e, ?_⟩
      have h := MulCongruenceInternal.liftCode_valid hsa hsb hra hrb hd' he'
      simpa [termSubstVec_cons₂ hs.isUTerm hr.isUTerm,MulCongruenceInternal.mulTerm] using h
#print axioms reflexive
#print axioms replace
end PA194PAeq.TermCongruence
