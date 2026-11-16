import PA194ContextConjunctionCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextModusPonensCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode PA194ContextConjunctionCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Explicit cut-based modus ponens proof code under a shared context. -/
noncomputable def contextMPCode (p q g di dp : M) : M :=
  let implication := neg SourceL p ^⋎ q
  let nq := neg SourceL q
  let target := insert q g
  let negContext := insert (p ^⋏ nq) target
  let wp := wkRule (insert p negContext) dp
  let en := axL (insert nq negContext) q
  let dn := andIntro negContext p nq wp en
  let wi := wkRule (insert implication target) di
  cutRule target implication wi dn

noncomputable def contextMPGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g di dp. ∃ np, !(negGraph SourceL) np p ∧ ∃ imp, !qqOrDef imp np q ∧
    ∃ nq, !(negGraph SourceL) nq q ∧ ∃ target, !insertDef target q g ∧
    ∃ npq, !qqAndDef npq p nq ∧ ∃ nctx, !insertDef nctx npq target ∧
    ∃ ps, !insertDef ps p nctx ∧ ∃ wp, !wkRuleGraph wp ps dp ∧
    ∃ ns, !insertDef ns nq nctx ∧ ∃ en, !axLGraph en ns q ∧
    ∃ dn, !andIntroGraph dn nctx p nq wp en ∧
    ∃ is, !insertDef is imp target ∧ ∃ wi, !wkRuleGraph wi is di ∧
      !cutRuleGraph out target imp wi dn”

theorem contextMPGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextMPCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextMPGraph := .mk fun v => by
  simp [contextMPGraph,contextMPCode]

noncomputable def contextMPProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (di : T ⊢!ᵈᵉʳ insert (p 🡒 q) Γ) (dp : T ⊢!ᵈᵉʳ insert p Γ) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let target : Sequent M SourceL := insert q Γ
  let negContext : Sequent M SourceL := insert (p ⋏ ∼q) target
  let wp : T ⊢!ᵈᵉʳ insert p negContext :=
    TDerivation.wk dp (by intro x hx; simp [negContext,target] at hx ⊢; tauto)
  let en : T ⊢!ᵈᵉʳ insert (∼q) negContext :=
    TDerivation.em q (by simp [negContext,target]) (by simp)
  let dn : T ⊢!ᵈᵉʳ negContext := TDerivation.and' (by simp [negContext]) wp en
  let wi : T ⊢!ᵈᵉʳ insert (p 🡒 q) target :=
    TDerivation.wk di (by intro x hx; simp [target] at hx ⊢; tauto)
  have hdn : DerivationOf T.theory dn.val (insert (neg SourceL (p 🡒 q).val) target.val) := by
    have h := dn.derivationOf
    simpa [negContext,Semiformula.imp_def,DeMorgan.or,DeMorgan.neg] using h
  have hcut : Derivation T.theory (cutRule target.val (p 🡒 q).val wi.val dn.val) :=
    Derivation.cutRule wi.derivationOf hdn
  refine ⟨contextMPCode p.val q.val Γ.val di.val dp.val, ?_⟩
  have hcode : contextMPCode p.val q.val Γ.val di.val dp.val =
      cutRule target.val (p 🡒 q).val wi.val dn.val := by
    simp [contextMPCode, target, negContext, wp, en, dn, wi, Semiformula.imp_def]
  constructor
  · simp [contextMPCode]
  · rw [hcode]
    exact hcut

@[simp] theorem contextMPProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (di : T ⊢!ᵈᵉʳ insert (p 🡒 q) Γ) (dp : T ⊢!ᵈᵉʳ insert p Γ) :
    (contextMPProof T Γ p q di dp).val = contextMPCode p.val q.val Γ.val di.val dp.val := rfl

#print axioms contextMPGraph_defined
#print axioms contextMPProof
#print axioms contextMPProof_val
end models
end PA194ContextModusPonensCode
