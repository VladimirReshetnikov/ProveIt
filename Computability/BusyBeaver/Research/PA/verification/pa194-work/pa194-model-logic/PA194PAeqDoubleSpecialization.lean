import PA194PAeqModusPonens
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqDoubleSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Uniform proof-code composition for two universal instantiations. -/
noncomputable def paeqDoubleCode (p t u g d : V) : V :=
  let one := subst PA194PAeq.language (qVec PA194PAeq.language (?[u] : V)) p
  let first := paeqSpecializeCode (^∀ p) u g d
  paeqSpecializeCode one t g first

noncomputable def paeqDoubleGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p t u g d. ∃ v, !adjoinDef v u 0 ∧ ∃ q, !(qVecGraph PA194PAeq.language) q v ∧
    ∃ one, !(substsGraph PA194PAeq.language) one q p ∧ ∃ all, !qqAllDef all p ∧
    ∃ first, !paeqSpecializeGraph first all u g d ∧ !paeqSpecializeGraph out one t g first”

theorem paeqDoubleGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V => paeqDoubleCode (v 0) (v 1) (v 2) (v 3) (v 4)) paeqDoubleGraph := by
  haveI := paeqSpecializeGraph_defined (V := V)
  exact .mk fun v => by simp [paeqDoubleGraph,paeqDoubleCode]

noncomputable def paeqDoubleProof (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 2) (t u : Term V PA194PAeq.language)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u]) Γ := by
  let first := paeqSpecializeProof T Γ (∀⁰ p) u d
  have he1 : (∀⁰ p).subst ![u] = ∀⁰ p.subst (SemitermVec.q ![u]) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let second := paeqSpecializeProof T Γ (p.subst (SemitermVec.q ![u])) t first'
  have he2 : (p.subst (SemitermVec.q ![u])).subst ![t] = p.subst ![t,u] := by
    simp [Semiformula.substs_substs]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) second

@[simp] theorem paeqDoubleProof_val (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p : Semiformula V PA194PAeq.language 2) (t u : Term V PA194PAeq.language)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ p) Γ) :
    (paeqDoubleProof T Γ p t u d).val = paeqDoubleCode p.val t.val u.val Γ.val d.val := by
  simp [paeqDoubleProof,paeqDoubleCode,SemitermVec.val_succ,qVec]

#print axioms paeqDoubleGraph_defined
#print axioms paeqDoubleProof
#print axioms paeqDoubleProof_val
end PA194PAeqDoubleSpecialization
