import PA194PAeqTripleSpecialization
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqQuadSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization PA194PAeqTripleSpecialization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def paeqQuadCode (p t u v w g d : V) : V :=
  let one := subst PA194PAeq.language (qVec PA194PAeq.language (qVec PA194PAeq.language (qVec PA194PAeq.language (?[w] : V)))) p
  let first := paeqSpecializeCode (^∀ ^∀ ^∀ p) w g d
  paeqTripleCode one t u v g first
noncomputable def paeqQuadGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out p t u v w g d. ∃ vec q1 q2 q3 one all1 all2 all3 first,
    !adjoinDef vec w 0 ∧ !(qVecGraph PA194PAeq.language) q1 vec ∧
    !(qVecGraph PA194PAeq.language) q2 q1 ∧ !(qVecGraph PA194PAeq.language) q3 q2 ∧
    !(substsGraph PA194PAeq.language) one q3 p ∧
    !qqAllDef all1 p ∧ !qqAllDef all2 all1 ∧ !qqAllDef all3 all2 ∧
    !paeqSpecializeGraph first all3 w g d ∧ !paeqTripleGraph out one t u v g first”
theorem paeqQuadGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → V => paeqQuadCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) paeqQuadGraph := by
  haveI := paeqSpecializeGraph_defined (V := V)
  haveI := paeqTripleGraph_defined (V := V)
  exact .mk fun v => by simp [paeqQuadGraph,paeqQuadCode]
noncomputable def paeqQuadProof (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 4) (t u v w : Term V PA194PAeq.language)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u,v,w]) Γ := by
  let first := paeqSpecializeProof T Γ (∀⁰ ∀⁰ ∀⁰ p) w d
  have he1 : (∀⁰ ∀⁰ ∀⁰ p).subst ![w] = ∀⁰ ∀⁰ ∀⁰ p.subst (SemitermVec.q (SemitermVec.q (SemitermVec.q ![w]))) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let second := paeqTripleProof T Γ (p.subst (SemitermVec.q (SemitermVec.q (SemitermVec.q ![w])))) t u v first'
  have he2 : (p.subst (SemitermVec.q (SemitermVec.q (SemitermVec.q ![w])))).subst ![t,u,v] = p.subst ![t,u,v,w] := by
    simp [Semiformula.substs_substs,Semiterm.bShift_substs_succ]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) second
@[simp] theorem paeqQuadProof_val (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 4) (t u v w : Term V PA194PAeq.language)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ p) Γ) :
    (paeqQuadProof T Γ p t u v w d).val = paeqQuadCode p.val t.val u.val v.val w.val Γ.val d.val := by
  have hv : IsUTerm PA194PAeq.language (termBShift PA194PAeq.language w.val) := w.isSemiterm.termBShift.isUTerm
  have hvv : IsUTerm PA194PAeq.language (termBShift PA194PAeq.language (termBShift PA194PAeq.language w.val)) := w.isSemiterm.termBShift.termBShift.isUTerm
  simp [paeqQuadProof,paeqQuadCode,SemitermVec.val_succ,qVec,
    one_add_one_eq_two,show (3:V)=2+1 from two_add_one_eq_three.symm,
    termBShiftVec_cons₂,termBShiftVec_cons,hv,hvv]
#print axioms paeqQuadGraph_defined
#print axioms paeqQuadProof
#print axioms paeqQuadProof_val
end PA194PAeqQuadSpecialization
