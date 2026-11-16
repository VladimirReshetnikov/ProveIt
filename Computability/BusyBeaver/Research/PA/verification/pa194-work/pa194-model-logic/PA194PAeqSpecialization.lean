import PA194PAeqAddOneProofInternal
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Explicit one-binder specialization proof code under a shared context. -/
noncomputable def paeqSpecializeCode (p t g d : V) : V :=
  let inst := substs1 PA194PAeq.language t p
  let np := neg PA194PAeq.language p
  let ninst := neg PA194PAeq.language inst
  let all := ^∀ p
  let nex := ^∃ np
  let target := insert inst g
  let u := insert nex target
  let en := axL (insert ninst u) inst
  let ex := exsIntro u np t en
  let wd := wkRule (insert all target) d
  cutRule target all wd ex

noncomputable def paeqSpecializeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p t g d. ∃ inst, !(substs1Graph PA194PAeq.language) inst t p ∧ ∃ np, !(negGraph PA194PAeq.language) np p ∧
    ∃ ni, !(negGraph PA194PAeq.language) ni inst ∧ ∃ al, !qqAllDef al p ∧ ∃ ne, !qqExsDef ne np ∧
    ∃ target, !insertDef target inst g ∧ ∃ u, !insertDef u ne target ∧
    ∃ ns, !insertDef ns ni u ∧ ∃ en, !axLGraph en ns inst ∧ ∃ ex, !exsIntroGraph ex u np t en ∧
    ∃ as, !insertDef as al target ∧ ∃ wd, !wkRuleGraph wd as d ∧ !cutRuleGraph out target al wd ex”

theorem paeqSpecializeGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → V => paeqSpecializeCode (v 0) (v 1) (v 2) (v 3)) paeqSpecializeGraph := .mk fun v => by
  simp [paeqSpecializeGraph,paeqSpecializeCode]

noncomputable def paeqSpecializeProof (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 1) (t : Term V PA194PAeq.language) (d : T ⊢!ᵈᵉʳ insert (∀⁰ p) Γ) :
    T ⊢!ᵈᵉʳ insert (p.subst ![t]) Γ := by
  let inst : Formula V PA194PAeq.language := p.subst ![t]
  let np : Semiformula V PA194PAeq.language 1 := ∼p
  let target : Sequent V PA194PAeq.language := insert inst Γ
  let u : Sequent V PA194PAeq.language := insert (∃⁰ np) target
  let en : T ⊢!ᵈᵉʳ insert (∼inst) u :=
    TDerivation.em inst (by simp [u,target]) (by simp)
  have hsub : substs1 PA194PAeq.language t.val np.val = neg PA194PAeq.language inst.val := by
    have hw : IsSemitermVec PA194PAeq.language 1 0 (?[t.val] : V) := by
      simpa using (show (SemitermVec.val ![t]).isSemitermVec from (SemitermVec.isSemitermVec ![t]))
    have hp : IsSemiformula PA194PAeq.language 1 p.val := by simpa using p.isSemiformula
    simpa [inst,np,substs1] using (substs_neg hp hw)
  have hen : DerivationOf T.theory en.val (insert (substs1 PA194PAeq.language t.val np.val) u.val) := by
    rw [hsub]
    exact en.derivationOf
  have hex : Derivation T.theory (exsIntro u.val np.val t.val en.val) :=
    Derivation.exsIntro (by simp [u]) t.isSemiterm hen
  let wd : T ⊢!ᵈᵉʳ insert (∀⁰ p) target :=
    TDerivation.wk d (by intro x hx; simp [target] at hx ⊢; tauto)
  have hneg : DerivationOf T.theory (exsIntro u.val np.val t.val en.val)
      (insert (neg PA194PAeq.language (∀⁰ p).val) target.val) := by
    constructor
    · simp [u,np,Bootstrapping.Semiformula.neg_all]
    · exact hex
  have hcut : Derivation T.theory (cutRule target.val (∀⁰ p).val wd.val (exsIntro u.val np.val t.val en.val)) :=
    Derivation.cutRule wd.derivationOf hneg
  refine ⟨paeqSpecializeCode p.val t.val Γ.val d.val, ?_⟩
  have hcode : paeqSpecializeCode p.val t.val Γ.val d.val =
      cutRule target.val (∀⁰ p).val wd.val (exsIntro u.val np.val t.val en.val) := by
    simp [paeqSpecializeCode,inst,np,target,u,en,wd,substs1,SemitermVec.val_succ]
  constructor
  · simp [paeqSpecializeCode, substs1]
  · rw [hcode]
    exact hcut

@[simp] theorem paeqSpecializeProof_val (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 1) (t : Term V PA194PAeq.language) (d : T ⊢!ᵈᵉʳ insert (∀⁰ p) Γ) :
    (paeqSpecializeProof T Γ p t d).val = paeqSpecializeCode p.val t.val Γ.val d.val := rfl

#print axioms paeqSpecializeGraph_defined
#print axioms paeqSpecializeProof
#print axioms paeqSpecializeProof_val
end PA194PAeqSpecialization
