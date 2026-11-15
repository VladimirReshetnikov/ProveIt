import PA194ContextSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextAllCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Universal introduction under an arbitrary context, with a fresh free variable. -/
noncomputable def contextAllCode (p g d : M) : M :=
  let target := insert (^∀ p) g
  let body := free SourceL p
  let premise := insert body (setShift SourceL target)
  let wd := wkRule premise d
  allIntro target p wd

noncomputable def contextAllGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out p g d. ∃ all, !qqAllDef all p ∧ ∃ target, !insertDef target all g ∧
    ∃ body, !(freeGraph SourceL) body p ∧ ∃ sh, !(setShiftGraph SourceL) sh target ∧
    ∃ premise, !insertDef premise body sh ∧ ∃ wd, !wkRuleGraph wd premise d ∧
    !allIntroGraph out target p wd”

theorem contextAllGraph_defined :
    𝚺₁-Function₃ (contextAllCode : M → M → M → M) via contextAllGraph := by
  exact .mk fun v => by simp [contextAllGraph,contextAllCode]

noncomputable def contextAllProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (d : T ⊢!ᵈᵉʳ insert p.free Γ.shift) :
    T ⊢!ᵈᵉʳ insert (∀⁰ p) Γ := by
  let target := insert (∀⁰ p) Γ
  have incl : insert p.free Γ.shift ⊆ insert p.free target.shift := by
    intro q hq
    simp [target, Sequent.shift, mem_setShift_insert] at hq ⊢
    tauto
  let wd := TDerivation.wk d incl
  exact TDerivation.all' (by simp [target]) wd

@[simp] theorem contextAllProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (d : T ⊢!ᵈᵉʳ insert p.free Γ.shift) :
    (contextAllProof T Γ p d).val = contextAllCode p.val Γ.val d.val := by
  simp [contextAllProof,contextAllCode,Sequent.shift]

#print axioms contextAllGraph_defined
#print axioms contextAllProof
#print axioms contextAllProof_val
end models
end PA194ContextAllCode
