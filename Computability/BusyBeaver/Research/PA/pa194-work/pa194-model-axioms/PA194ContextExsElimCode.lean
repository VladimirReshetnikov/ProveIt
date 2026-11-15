import PA194ContextAllCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextExsElimCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextAllCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Existential elimination using an explicitly shifted eigenvariable context. -/
noncomputable def contextExsElimCode (p q g de db : M) : M :=
  let target := insert q g
  let ex := ^∃ p
  let np := neg SourceL p
  let we := wkRule (insert ex target) de
  let branch := contextAllCode np target db
  cutRule target ex we branch

noncomputable def contextExsElimGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p q g de db. ∃ target, !insertDef target q g ∧ ∃ ex, !qqExsDef ex p ∧
    ∃ np, !(negGraph SourceL) np p ∧ ∃ ext, !insertDef ext ex target ∧
    ∃ we, !wkRuleGraph we ext de ∧ ∃ branch, !contextAllGraph branch np target db ∧
    !cutRuleGraph out target ex we branch”

theorem contextExsElimGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextExsElimCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextExsElimGraph := by
  haveI := contextAllGraph_defined (M := M)
  exact .mk fun v => by simp [contextExsElimGraph, contextExsElimCode]

noncomputable def contextExsElimProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert (∃⁰ p) Γ)
    (db : T ⊢!ᵈᵉʳ insert (∼p).free (insert q Γ).shift) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let target := insert q Γ
  let we : T ⊢!ᵈᵉʳ insert (∃⁰ p) target :=
    TDerivation.wk de (by intro x hx; simp [target] at hx ⊢; tauto)
  let branch := contextAllProof T target (∼p) db
  have hbranch : DerivationOf T.theory branch.val (insert (neg SourceL (∃⁰ p).val) target.val) := by
    have h := branch.derivationOf
    simpa using h
  have hcut : Derivation T.theory (cutRule target.val (∃⁰ p).val we.val branch.val) :=
    Derivation.cutRule we.derivationOf hbranch
  refine ⟨contextExsElimCode p.val q.val Γ.val de.val db.val, ?_⟩
  have he : contextExsElimCode p.val q.val Γ.val de.val db.val =
      cutRule target.val (∃⁰ p).val we.val branch.val := by
    simp [contextExsElimCode,target,we,branch]
  constructor
  · simp [contextExsElimCode]
  · rw [he]; exact hcut

@[simp] theorem contextExsElimProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert (∃⁰ p) Γ)
    (db : T ⊢!ᵈᵉʳ insert (∼p).free (insert q Γ).shift) :
    (contextExsElimProof T Γ p q de db).val = contextExsElimCode p.val q.val Γ.val de.val db.val := rfl

#print axioms contextExsElimGraph_defined
#print axioms contextExsElimProof
#print axioms contextExsElimProof_val
end models
end PA194ContextExsElimCode
