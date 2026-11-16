import PA194ContextSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextDoubleSpecializeCode
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

/-- Uniform proof-code composition for two universal instantiations. -/
noncomputable def contextDoubleCode (p t u g d : M) : M :=
  let one := subst SourceL (qVec SourceL (?[u] : M)) p
  let first := contextSpecializeCode (^∀ p) u g d
  contextSpecializeCode one t g first

noncomputable def contextDoubleGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p t u g d. ∃ v, !adjoinDef v u 0 ∧ ∃ q, !(qVecGraph SourceL) q v ∧
    ∃ one, !(substsGraph SourceL) one q p ∧ ∃ all, !qqAllDef all p ∧
    ∃ first, !contextSpecializeGraph first all u g d ∧ !contextSpecializeGraph out one t g first”

theorem contextDoubleGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => contextDoubleCode (v 0) (v 1) (v 2) (v 3) (v 4)) contextDoubleGraph := by
  haveI := contextSpecializeGraph_defined (M := M)
  exact .mk fun v => by simp [contextDoubleGraph,contextDoubleCode]

noncomputable def contextDoubleProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 2) (t u : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u]) Γ := by
  let first := contextSpecializeProof T Γ (∀⁰ p) u d
  have he1 : (∀⁰ p).subst ![u] = ∀⁰ p.subst (SemitermVec.q ![u]) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let second := contextSpecializeProof T Γ (p.subst (SemitermVec.q ![u])) t first'
  have he2 : (p.subst (SemitermVec.q ![u])).subst ![t] = p.subst ![t,u] := by
    simp [Semiformula.substs_substs]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) second

@[simp] theorem contextDoubleProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 2) (t u : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ p) Γ) :
    (contextDoubleProof T Γ p t u d).val = contextDoubleCode p.val t.val u.val Γ.val d.val := by
  simp [contextDoubleProof,contextDoubleCode,SemitermVec.val_succ,qVec]

#print axioms contextDoubleGraph_defined
#print axioms contextDoubleProof
#print axioms contextDoubleProof_val
end models
end PA194ContextDoubleSpecializeCode
