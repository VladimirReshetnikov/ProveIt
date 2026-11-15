import PA194PAeqUniversalTermCongruence
import PA194PAeqAtomicCongruence
import PA194PAeqSymmetryLift
import Foundation.Meta.ClProver
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.ContextCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem symmetry_imp {t u : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) :
    Provable ordinaryPAeq (imp language (equalityCode t u) (equalityCode u t)) := by
  refine ⟨Symmetry.atTermsCode u t, ?_⟩
  have h := Symmetry.atTermsCode_valid hu ht
  rw [Symmetry.body_subst hu ht] at h
  simpa [Theory.internalize] using h

theorem context_symmetry (Γ : Sequent V language) {t u : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hd : Derivable ordinaryPAeq (insert (equalityCode t u) Γ.val)) :
    Derivable ordinaryPAeq (insert (equalityCode u t) Γ.val) :=
  context_mp Γ (equality_valid ht hu) (equality_valid hu ht) (symmetry_imp ht hu) hd

theorem context_transitivity (Γ : Sequent V language) {t u v : V}
    (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) (hv : IsSemiterm language 0 v)
    (hd : Derivable ordinaryPAeq (insert (equalityCode t u) Γ.val))
    (he : Derivable ordinaryPAeq (insert (equalityCode u v) Γ.val)) :
    Derivable ordinaryPAeq (insert (equalityCode t v) Γ.val) := by
  have hp := equality_valid ht hu
  have hq := equality_valid hu hv
  have hr := equality_valid ht hv
  have hi : IsSemiformula language 0 (imp language (equalityCode u v) (equalityCode t v)) := IsSemiformula.imp.mpr ⟨hq,hr⟩
  have first := context_mp Γ hp hi (AtomicCongruence.transitivity_imp ht hu hv) hd
  exact context_mp_both Γ hq hr first he
theorem atomic_implication {a b s t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (hs : IsSemiterm language 1 s) (ht : IsSemiterm language 1 t) :
    Provable ordinaryPAeq (imp language (equalityCode a b)
      (imp language (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t))
        (equalityCode (termSubst language (b∷(0:V)) s) (termSubst language (b∷(0:V)) t)))) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  have hva : IsSemitermVec language 1 0 (a∷(0:V)) := by simp [ha]
  have hvb : IsSemitermVec language 1 0 (b∷(0:V)) := by simp [hb]
  let sa := termSubst language (a∷(0:V)) s
  let sb := termSubst language (b∷(0:V)) s
  let ta := termSubst language (a∷(0:V)) t
  let tb := termSubst language (b∷(0:V)) t
  have hsa := hva.termSubst hs
  have hsb := hvb.termSubst hs
  have hta := hva.termSubst ht
  have htb := hvb.termSubst ht
  let P : Formula V language := ⟨equalityCode a b,equality_valid ha hb⟩
  let A : Formula V language := ⟨equalityCode sa ta,equality_valid hsa hta⟩
  let B : Formula V language := ⟨equalityCode sb tb,equality_valid hsb htb⟩
  let Γ : Sequent V language := insert (∼P) (insert (∼A) ∅)
  let seedP : T ⊢!ᵈᵉʳ insert P Γ := TDerivation.em P (by simp) (by simp [Γ])
  let seedA : T ⊢!ᵈᵉʳ insert A Γ := TDerivation.em A (by simp) (by simp [Γ])
  have hp : Derivable ordinaryPAeq (insert (equalityCode a b) Γ.val) := by
    simpa [T,P,instΔ₁Theory] using seedP.toDerivable
  have hatom : Derivable ordinaryPAeq (insert (equalityCode sa ta) Γ.val) := by
    simpa [T,A,instΔ₁Theory] using seedA.toDerivable
  have hss : Derivable ordinaryPAeq (insert (equalityCode sa sb) Γ.val) := term_replace Γ ha hb hs hp
  have htt : Derivable ordinaryPAeq (insert (equalityCode ta tb) Γ.val) := term_replace Γ ha hb ht hp
  have hback := context_symmetry Γ hsa hsb hss
  have hm := context_transitivity Γ hsb hsa hta hback hatom
  have hout := context_transitivity Γ hsb hta htb hm htt
  let out : T ⊢!ᵈᵉʳ insert B Γ := Derivable.toTDerivation _ (by simpa [T,B,instΔ₁Theory] using hout)
  have d1 : T ⊢!ᵈᵉʳ insert (∼A) (insert B (insert (∼P) ∅)) :=
    TDerivation.wk out (by intro x hx; simp [Γ] at hx ⊢; tauto)
  let e1 := TDerivation.or d1
  have d2 : T ⊢!ᵈᵉʳ insert (∼P) (insert (A 🡒 B) ∅) :=
    TDerivation.wk (by simpa [Semiformula.imp_def] using e1) (by intro x hx; simp at hx ⊢; tauto)
  let e2 := TDerivation.or d2
  refine ⟨e2.val, ?_⟩
  simpa [T,P,A,B,sa,sb,ta,tb,Proof,instΔ₁Theory,Semiformula.imp_def,imp,← singleton_eq_insert] using e2.derivationOf

theorem negative_atomic_implication {a b s t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (hs : IsSemiterm language 1 s) (ht : IsSemiterm language 1 t) :
    Provable ordinaryPAeq (imp language (equalityCode a b)
      (imp language (neg language (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t)))
        (neg language (equalityCode (termSubst language (b∷(0:V)) s) (termSubst language (b∷(0:V)) t))))) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  have hva : IsSemitermVec language 1 0 (a∷(0:V)) := by simp [ha]
  have hvb : IsSemitermVec language 1 0 (b∷(0:V)) := by simp [hb]
  let P : Formula V language := ⟨equalityCode a b,equality_valid ha hb⟩
  let R : Formula V language := ⟨equalityCode b a,equality_valid hb ha⟩
  let A : Formula V language := ⟨equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t),
    equality_valid (hva.termSubst hs) (hva.termSubst ht)⟩
  let B : Formula V language := ⟨equalityCode (termSubst language (b∷(0:V)) s) (termSubst language (b∷(0:V)) t),
    equality_valid (hvb.termSubst hs) (hvb.termSubst ht)⟩
  have hsym : T ⊢ P 🡒 R := (TProvable.iff_provable).mpr (by simpa [P,R,Semiformula.imp_def,imp] using symmetry_imp ha hb)
  have hatom : T ⊢ R 🡒 (B 🡒 A) := (TProvable.iff_provable).mpr (by simpa [R,A,B,Semiformula.imp_def,imp] using atomic_implication hb ha hs ht)
  have out : T ⊢ P 🡒 (∼A 🡒 ∼B) := by cl_prover [hsym,hatom]
  have hr := (TProvable.iff_provable).mp out
  have hnn : neg language (neg language (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t))) =
      equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t) :=
    (equality_valid (hva.termSubst hs) (hva.termSubst ht)).isUFormula.neg_neg
  simpa [T,P,R,A,B,Semiformula.imp_def,Semiformula.val_neg,imp,hnn] using hr

#print axioms negative_atomic_implication
#print axioms atomic_implication
#print axioms symmetry_imp
#print axioms context_symmetry
#print axioms context_transitivity
end PA194PAeq.ContextCongruence
