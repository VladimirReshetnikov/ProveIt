import PA194ContextModusPonensCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextContradictionCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode
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

/-- Contradictory contextual proofs imply any contextual conclusion. -/
noncomputable def contextContradictionCode (p q g dp dn : M) : M :=
  let target := insert q g
  let np := neg SourceL p
  let wp := wkRule (insert p target) dp
  let wn := wkRule (insert np target) dn
  cutRule target p wp wn

noncomputable def contextContradictionGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g dp dn. ∃ target, !insertDef target q g ∧ ∃ np, !(negGraph SourceL) np p ∧
    ∃ ps, !insertDef ps p target ∧ ∃ wp, !wkRuleGraph wp ps dp ∧
    ∃ ns, !insertDef ns np target ∧ ∃ wn, !wkRuleGraph wn ns dn ∧
    !cutRuleGraph out target p wp wn”

theorem contextContradictionGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextContradictionCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextContradictionGraph := by
  exact .mk fun v => by simp [contextContradictionGraph,contextContradictionCode]

noncomputable def contextContradictionProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (dp : T ⊢!ᵈᵉʳ insert p Γ) (dn : T ⊢!ᵈᵉʳ insert (∼p) Γ) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let target := insert q Γ
  let wp : T ⊢!ᵈᵉʳ insert p target := TDerivation.wk dp (by intro x hx; simp [target] at hx ⊢; tauto)
  let wn : T ⊢!ᵈᵉʳ insert (∼p) target := TDerivation.wk dn (by intro x hx; simp [target] at hx ⊢; tauto)
  have hcut : Derivation T.theory (cutRule target.val p.val wp.val wn.val) :=
    Derivation.cutRule wp.derivationOf wn.derivationOf
  refine ⟨contextContradictionCode p.val q.val Γ.val dp.val dn.val, ?_⟩
  have he : contextContradictionCode p.val q.val Γ.val dp.val dn.val = cutRule target.val p.val wp.val wn.val := by
    simp [contextContradictionCode,target,wp,wn]
  constructor
  · simp [contextContradictionCode]
  · rw [he]; exact hcut

@[simp] theorem contextContradictionProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (dp : T ⊢!ᵈᵉʳ insert p Γ) (dn : T ⊢!ᵈᵉʳ insert (∼p) Γ) :
    (contextContradictionProof T Γ p q dp dn).val = contextContradictionCode p.val q.val Γ.val dp.val dn.val := rfl

#print axioms contextContradictionGraph_defined
#print axioms contextContradictionProof
#print axioms contextContradictionProof_val
end models
end PA194ContextContradictionCode
