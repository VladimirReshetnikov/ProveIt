import PA194PAeqSpecialization
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqModusPonens
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Explicit cut-based modus ponens proof code under a shared context. -/
noncomputable def paeqMPCode (p q g di dp : V) : V :=
  let implication := neg PA194PAeq.language p ^⋎ q
  let nq := neg PA194PAeq.language q
  let target := insert q g
  let negContext := insert (p ^⋏ nq) target
  let wp := wkRule (insert p negContext) dp
  let en := axL (insert nq negContext) q
  let dn := andIntro negContext p nq wp en
  let wi := wkRule (insert implication target) di
  cutRule target implication wi dn

noncomputable def paeqMPGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g di dp. ∃ np, !(negGraph PA194PAeq.language) np p ∧ ∃ imp, !qqOrDef imp np q ∧
    ∃ nq, !(negGraph PA194PAeq.language) nq q ∧ ∃ target, !insertDef target q g ∧
    ∃ npq, !qqAndDef npq p nq ∧ ∃ nctx, !insertDef nctx npq target ∧
    ∃ ps, !insertDef ps p nctx ∧ ∃ wp, !wkRuleGraph wp ps dp ∧
    ∃ ns, !insertDef ns nq nctx ∧ ∃ en, !axLGraph en ns q ∧
    ∃ dn, !andIntroGraph dn nctx p nq wp en ∧
    ∃ is, !insertDef is imp target ∧ ∃ wi, !wkRuleGraph wi is di ∧
      !cutRuleGraph out target imp wi dn”

theorem paeqMPGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → V => paeqMPCode (v 0) (v 1) (v 2) (v 3) (v 4)) paeqMPGraph := .mk fun v => by
  simp [paeqMPGraph,paeqMPCode]

noncomputable def paeqMPProof (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p q : Formula V PA194PAeq.language) (di : T ⊢!ᵈᵉʳ insert (p 🡒 q) Γ) (dp : T ⊢!ᵈᵉʳ insert p Γ) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let target : Sequent V PA194PAeq.language := insert q Γ
  let negContext : Sequent V PA194PAeq.language := insert (p ⋏ ∼q) target
  let wp : T ⊢!ᵈᵉʳ insert p negContext :=
    TDerivation.wk dp (by intro x hx; simp [negContext,target] at hx ⊢; tauto)
  let en : T ⊢!ᵈᵉʳ insert (∼q) negContext :=
    TDerivation.em q (by simp [negContext,target]) (by simp)
  let dn : T ⊢!ᵈᵉʳ negContext := TDerivation.and' (by simp [negContext]) wp en
  let wi : T ⊢!ᵈᵉʳ insert (p 🡒 q) target :=
    TDerivation.wk di (by intro x hx; simp [target] at hx ⊢; tauto)
  have hdn : DerivationOf T.theory dn.val (insert (neg PA194PAeq.language (p 🡒 q).val) target.val) := by
    have h := dn.derivationOf
    simpa [negContext,Semiformula.imp_def,DeMorgan.or,DeMorgan.neg] using h
  have hcut : Derivation T.theory (cutRule target.val (p 🡒 q).val wi.val dn.val) :=
    Derivation.cutRule wi.derivationOf hdn
  refine ⟨paeqMPCode p.val q.val Γ.val di.val dp.val, ?_⟩
  have hcode : paeqMPCode p.val q.val Γ.val di.val dp.val =
      cutRule target.val (p 🡒 q).val wi.val dn.val := by
    simp [paeqMPCode, target, negContext, wp, en, dn, wi, Semiformula.imp_def]
  constructor
  · simp [paeqMPCode]
  · rw [hcode]
    exact hcut

@[simp] theorem paeqMPProof_val (T : InternalTheory V PA194PAeq.language) (Γ : Sequent V PA194PAeq.language)
    (p q : Formula V PA194PAeq.language) (di : T ⊢!ᵈᵉʳ insert (p 🡒 q) Γ) (dp : T ⊢!ᵈᵉʳ insert p Γ) :
    (paeqMPProof T Γ p q di dp).val = paeqMPCode p.val q.val Γ.val di.val dp.val := rfl

#print axioms paeqMPGraph_defined
#print axioms paeqMPProof
#print axioms paeqMPProof_val
end PA194PAeqModusPonens
