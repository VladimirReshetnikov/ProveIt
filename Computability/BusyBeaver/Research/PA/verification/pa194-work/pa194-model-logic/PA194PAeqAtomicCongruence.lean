import PA194PAeqTermCongruence
import PA194PAeqSymmetryLift
import PA194PAeqTransitivityLift
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AtomicCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint Entailment Entailment.FiniteContext Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem transitivity_imp {x y z : V} (hx : IsSemiterm language 0 x) (hy : IsSemiterm language 0 y) (hz : IsSemiterm language 0 z) :
    Provable ordinaryPAeq (imp language (equalityCode x y) (imp language (equalityCode y z) (equalityCode x z))) := by
  refine ⟨Transitivity.atTermsCode z y x, ?_⟩
  have h := Transitivity.atTermsCode_valid hz hy hx
  rw [Transitivity.body_subst hz hy hx] at h
  simpa [Theory.internalize] using h

theorem atomic_replace {a b s t : V} (ha : IsSemiterm language 0 a) (hb : IsSemiterm language 0 b)
    (hs : IsSemiterm language 1 s) (ht : IsSemiterm language 1 t)
    (hab : Provable ordinaryPAeq (equalityCode a b)) :
    Provable ordinaryPAeq (imp language
      (equalityCode (termSubst language (a∷(0:V)) s) (termSubst language (a∷(0:V)) t))
      (equalityCode (termSubst language (b∷(0:V)) s) (termSubst language (b∷(0:V)) t))) := by
  let va := (a∷(0:V))
  let vb := (b∷(0:V))
  have hva : IsSemitermVec language 1 0 va := by simp [va,ha]
  have hvb : IsSemitermVec language 1 0 vb := by simp [vb,hb]
  let sa := termSubst language va s
  let sb := termSubst language vb s
  let ta := termSubst language va t
  let tb := termSubst language vb t
  have hsa : IsSemiterm language 0 sa := hva.termSubst hs
  have hsb : IsSemiterm language 0 sb := hvb.termSubst hs
  have hta : IsSemiterm language 0 ta := hva.termSubst ht
  have htb : IsSemiterm language 0 tb := hvb.termSubst ht
  have hss : Provable ordinaryPAeq (equalityCode sa sb) := TermCongruence.replace ha hb hs hab
  have htt : Provable ordinaryPAeq (equalityCode ta tb) := TermCongruence.replace ha hb ht hab
  obtain ⟨ds,hds⟩ := hss
  have hrev : Provable ordinaryPAeq (equalityCode sb sa) := ⟨_,Symmetry.liftCode_valid hsa hsb hds⟩
  have htr1 := transitivity_imp hsb hsa hta
  have htr2 := transitivity_imp hsb hta htb
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let A : Formula V language := ⟨equalityCode sa ta, equality_valid hsa hta⟩
  let B : Formula V language := ⟨equalityCode sb tb, equality_valid hsb htb⟩
  let X : Formula V language := ⟨equalityCode sb sa, equality_valid hsb hsa⟩
  let Y : Formula V language := ⟨equalityCode ta tb, equality_valid hta htb⟩
  let Z : Formula V language := ⟨equalityCode sb ta, equality_valid hsb hta⟩
  have hx : T ⊢ X := (TProvable.iff_provable).mpr hrev
  have hy : T ⊢ Y := (TProvable.iff_provable).mpr htt
  have h1 : T ⊢ X 🡒 A 🡒 Z := (TProvable.iff_provable).mpr (by simpa [X,A,Z,Semiformula.imp_def,imp] using htr1)
  have h2 : T ⊢ Z 🡒 Y 🡒 B := (TProvable.iff_provable).mpr (by simpa [Z,Y,B,Semiformula.imp_def,imp] using htr2)
  have hab' : T ⊢ A 🡒 B := by
    apply deduct'!
    have ha' : [A] ⊢[T] A := by_axm₀!
    have hx' : [A] ⊢[T] X := of'! hx
    have hy' : [A] ⊢[T] Y := of'! hy
    have h1' : [A] ⊢[T] X 🡒 A 🡒 Z := of'! h1
    have h2' : [A] ⊢[T] Z 🡒 Y 🡒 B := of'! h2
    exact h2' ⨀ (h1' ⨀ hx' ⨀ ha') ⨀ hy'
  have h := (TProvable.iff_provable).mp hab'
  simpa [T,A,B,sa,sb,ta,tb,va,vb,Semiformula.imp_def,imp] using h
#print axioms transitivity_imp
#print axioms atomic_replace
end PA194PAeq.AtomicCongruence
