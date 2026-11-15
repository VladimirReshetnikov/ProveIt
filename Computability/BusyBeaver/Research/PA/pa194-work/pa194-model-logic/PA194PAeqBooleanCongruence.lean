import PA194PAeqNegativeAtomicCongruence
import Foundation.Meta.ClProver
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.BooleanCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Entailment Entailment.FiniteContext Classical
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem and_imp {p q r s : V} (hp : IsSemiformula language 0 p) (hq : IsSemiformula language 0 q)
    (hr : IsSemiformula language 0 r) (hs : IsSemiformula language 0 s)
    (hpr : Provable ordinaryPAeq (imp language p r)) (hqs : Provable ordinaryPAeq (imp language q s)) :
    Provable ordinaryPAeq (imp language (p ^⋏ q) (r ^⋏ s)) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula V language := ⟨p,hp⟩
  let Q : Formula V language := ⟨q,hq⟩
  let R : Formula V language := ⟨r,hr⟩
  let S : Formula V language := ⟨s,hs⟩
  have h1 : T ⊢ P 🡒 R := (TProvable.iff_provable).mpr (by simpa [P,R,Semiformula.imp_def,imp] using hpr)
  have h2 : T ⊢ Q 🡒 S := (TProvable.iff_provable).mpr (by simpa [Q,S,Semiformula.imp_def,imp] using hqs)
  have hh : T ⊢ (P ⋏ Q) 🡒 (R ⋏ S) := by cl_prover [h1,h2]
  have h := (TProvable.iff_provable).mp hh
  simpa [T,P,Q,R,S,Semiformula.imp_def,imp,neg_and hp.isUFormula hq.isUFormula,neg_or hp.isUFormula hq.isUFormula] using h

theorem or_imp {p q r s : V} (hp : IsSemiformula language 0 p) (hq : IsSemiformula language 0 q)
    (hr : IsSemiformula language 0 r) (hs : IsSemiformula language 0 s)
    (hpr : Provable ordinaryPAeq (imp language p r)) (hqs : Provable ordinaryPAeq (imp language q s)) :
    Provable ordinaryPAeq (imp language (p ^⋎ q) (r ^⋎ s)) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Formula V language := ⟨p,hp⟩
  let Q : Formula V language := ⟨q,hq⟩
  let R : Formula V language := ⟨r,hr⟩
  let S : Formula V language := ⟨s,hs⟩
  have h1 : T ⊢ P 🡒 R := (TProvable.iff_provable).mpr (by simpa [P,R,Semiformula.imp_def,imp] using hpr)
  have h2 : T ⊢ Q 🡒 S := (TProvable.iff_provable).mpr (by simpa [Q,S,Semiformula.imp_def,imp] using hqs)
  have hh : T ⊢ (P ⋎ Q) 🡒 (R ⋎ S) := by cl_prover [h1,h2]
  have h := (TProvable.iff_provable).mp hh
  simpa [T,P,Q,R,S,Semiformula.imp_def,imp,neg_and hp.isUFormula hq.isUFormula,neg_or hp.isUFormula hq.isUFormula] using h
theorem all_imp {p q : V} (hp : IsSemiformula language 1 p) (hq : IsSemiformula language 1 q)
    (h : Provable ordinaryPAeq (imp language (Bootstrapping.free language p) (Bootstrapping.free language q))) :
    Provable ordinaryPAeq (imp language (^∀ p) (^∀ q)) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Semiformula V language 1 := ⟨p,by simpa using hp⟩
  let Q : Semiformula V language 1 := ⟨q,by simpa using hq⟩
  have h0 : T ⊢ P.free 🡒 Q.free := (TProvable.iff_provable).mpr (by simpa [P,Q,Semiformula.imp_def,imp] using h)
  have h1 : ([] : List (Formula V language)) ⊢[T] P.free 🡒 Q.free := of'! h0
  have h2 : ([] : List (Formula V language)) ⊢[T] (∀⁰ P) 🡒 (∀⁰ Q) := by
    apply TProof.all_imp_all!
    simpa using h1
  have h3 : T ⊢ (∀⁰ P) 🡒 (∀⁰ Q) := ⟨Entailment.FiniteContext.emptyPrf h2.some⟩
  have hraw := (TProvable.iff_provable).mp h3
  simpa [T,P,Q,Semiformula.imp_def,imp,neg_all hp.isUFormula,neg_ex hp.isUFormula] using hraw

theorem exs_imp {p q : V} (hp : IsSemiformula language 1 p) (hq : IsSemiformula language 1 q)
    (h : Provable ordinaryPAeq (imp language (Bootstrapping.free language p) (Bootstrapping.free language q))) :
    Provable ordinaryPAeq (imp language (^∃ p) (^∃ q)) := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let P : Semiformula V language 1 := ⟨p,by simpa using hp⟩
  let Q : Semiformula V language 1 := ⟨q,by simpa using hq⟩
  have h0 : T ⊢ P.free 🡒 Q.free := (TProvable.iff_provable).mpr (by simpa [P,Q,Semiformula.imp_def,imp] using h)
  have h1 : ([] : List (Formula V language)) ⊢[T] P.free 🡒 Q.free := of'! h0
  have h2 : ([] : List (Formula V language)) ⊢[T] (∃⁰ P) 🡒 (∃⁰ Q) := by
    apply TProof.exs_imp_exs!
    simpa using h1
  have h3 : T ⊢ (∃⁰ P) 🡒 (∃⁰ Q) := ⟨Entailment.FiniteContext.emptyPrf h2.some⟩
  have hraw := (TProvable.iff_provable).mp h3
  simpa [T,P,Q,Semiformula.imp_def,imp,neg_all hp.isUFormula,neg_ex hp.isUFormula] using hraw

#print axioms all_imp
#print axioms exs_imp
#print axioms and_imp
#print axioms or_imp
end PA194PAeq.BooleanCongruence
