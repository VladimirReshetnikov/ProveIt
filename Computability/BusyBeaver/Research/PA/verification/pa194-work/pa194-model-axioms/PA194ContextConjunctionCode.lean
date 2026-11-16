import PA194ContextShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextConjunctionCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode
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

/-- Explicit source derivation code for conjunction under a shared context. -/
noncomputable def contextAndCode (p q g dp dq : M) : M :=
  let s := insert (p ^⋏ q) g
  andIntro s p q (wkRule (insert p s) dp) (wkRule (insert q s) dq)

noncomputable def contextAndGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g dp dq. ∃ c, !qqAndDef c p q ∧ ∃ s, !insertDef s c g ∧
    ∃ sp, !insertDef sp p s ∧ ∃ sq, !insertDef sq q s ∧
    ∃ wp, !wkRuleGraph wp sp dp ∧ ∃ wq, !wkRuleGraph wq sq dq ∧
      !andIntroGraph out s p q wp wq”

theorem contextAndGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextAndCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextAndGraph := .mk fun v => by
  simp [contextAndGraph,contextAndCode]

noncomputable def contextAndProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (dp : T ⊢!ᵈᵉʳ insert p Γ) (dq : T ⊢!ᵈᵉʳ insert q Γ) :
    T ⊢!ᵈᵉʳ insert (p ⋏ q) Γ := by
  let Δ : Sequent M SourceL := insert (p ⋏ q) Γ
  have hp : T ⊢!ᵈᵉʳ insert p Δ := TDerivation.wk dp (by intro x hx; simp [Δ] at hx ⊢; tauto)
  have hq : T ⊢!ᵈᵉʳ insert q Δ := TDerivation.wk dq (by intro x hx; simp [Δ] at hx ⊢; tauto)
  exact TDerivation.and' (by simp [Δ]) hp hq

@[simp] theorem contextAndProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (dp : T ⊢!ᵈᵉʳ insert p Γ) (dq : T ⊢!ᵈᵉʳ insert q Γ) :
    (contextAndProof T Γ p q dp dq).val = contextAndCode p.val q.val Γ.val dp.val dq.val := by
  rfl

#print axioms contextAndGraph_defined
#print axioms contextAndProof
#print axioms contextAndProof_val
end models
end PA194ContextConjunctionCode
