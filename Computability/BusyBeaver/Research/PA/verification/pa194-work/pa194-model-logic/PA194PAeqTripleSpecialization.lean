import PA194PAeqDoubleSpecialization
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTripleSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization PA194PAeqDoubleSpecialization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def paeqTripleCode (p t u v g d : V) : V :=
  let one := subst PA194PAeq.language (qVec PA194PAeq.language (qVec PA194PAeq.language (?[v] : V))) p
  let first := paeqSpecializeCode (^∀ ^∀ p) v g d
  paeqDoubleCode one t u g first
noncomputable def paeqTripleGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p t u v g d. ∃ vec q1 q2 one all1 all2 first,
    !adjoinDef vec v 0 ∧ !(qVecGraph PA194PAeq.language) q1 vec ∧
    !(qVecGraph PA194PAeq.language) q2 q1 ∧ !(substsGraph PA194PAeq.language) one q2 p ∧
    !qqAllDef all1 p ∧ !qqAllDef all2 all1 ∧
    !paeqSpecializeGraph first all2 v g d ∧ !paeqDoubleGraph out one t u g first”
theorem paeqTripleGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → V => paeqTripleCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) paeqTripleGraph := by
  haveI := paeqSpecializeGraph_defined (V := V)
  haveI := paeqDoubleGraph_defined (V := V)
  exact .mk fun v => by simp [paeqTripleGraph,paeqTripleCode]
noncomputable def paeqTripleProof (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 3) (t u v : Term V PA194PAeq.language)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u,v]) Γ := by
  let first := paeqSpecializeProof T Γ (∀⁰ ∀⁰ p) v d
  have he1 : (∀⁰ ∀⁰ p).subst ![v] = ∀⁰ ∀⁰ p.subst (SemitermVec.q (SemitermVec.q ![v])) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let second := paeqDoubleProof T Γ (p.subst (SemitermVec.q (SemitermVec.q ![v]))) t u first'
  have he2 : (p.subst (SemitermVec.q (SemitermVec.q ![v]))).subst ![t,u] = p.subst ![t,u,v] := by
    simp [Semiformula.substs_substs,Semiterm.bShift_substs_succ]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) second
@[simp] theorem paeqTripleProof_val (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 3) (t u v : Term V PA194PAeq.language)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ p) Γ) :
    (paeqTripleProof T Γ p t u v d).val = paeqTripleCode p.val t.val u.val v.val Γ.val d.val := by
  have hv : IsUTerm PA194PAeq.language (termBShift PA194PAeq.language v.val) := v.isSemiterm.termBShift.isUTerm
  simp [paeqTripleProof,paeqTripleCode,SemitermVec.val_succ,qVec,
    one_add_one_eq_two,termBShiftVec_cons₂,hv]
#print axioms paeqTripleGraph_defined
#print axioms paeqTripleProof
#print axioms paeqTripleProof_val
end PA194PAeqTripleSpecialization
