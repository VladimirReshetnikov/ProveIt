import PA194ContextTripleSpecializeCode
import PA194ContextDoubleSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextFourSpecializeCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextTripleSpecializeCode PA194ContextDoubleSpecializeCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

noncomputable def contextFourCode (p t u v s g d : M) : M :=
  let vec := (?[v,s] : M)
  let q1 := qVec SourceL vec
  let q2 := qVec SourceL q1
  let two := subst SourceL q2 p
  let first := contextDoubleCode (^∀ (^∀ p)) v s g d
  contextDoubleCode two t u g first

noncomputable def contextFourGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out p t u v s g d. ∃ svec, !adjoinDef svec s 0 ∧ ∃ vec, !adjoinDef vec v svec ∧
    ∃ q1, !(qVecGraph SourceL) q1 vec ∧ ∃ q2, !(qVecGraph SourceL) q2 q1 ∧
    ∃ two, !(substsGraph SourceL) two q2 p ∧ ∃ a1, !qqAllDef a1 p ∧ ∃ a2, !qqAllDef a2 a1 ∧
    ∃ first, !contextDoubleGraph first a2 v s g d ∧ !contextDoubleGraph out two t u g first”

theorem contextFourGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 7 → M => contextFourCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) contextFourGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  exact .mk fun w => by simp [contextFourGraph,contextFourCode]

noncomputable def contextFourProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 4) (t u v s : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u,v,s]) Γ := by
  let first := contextDoubleProof T Γ (∀⁰ ∀⁰ p) v s d
  have he1 : (∀⁰ ∀⁰ p).subst ![v,s] = ∀⁰ ∀⁰ p.subst (SemitermVec.q (SemitermVec.q ![v,s])) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let rest := contextDoubleProof T Γ (p.subst (SemitermVec.q (SemitermVec.q ![v,s]))) t u first'
  have he2 : (p.subst (SemitermVec.q (SemitermVec.q ![v,s]))).subst ![t,u] = p.subst ![t,u,v,s] := by
    simp [Semiformula.substs_substs, Semiterm.bShift_substs_succ]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) rest

@[simp] theorem contextFourProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 4) (t u v s : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ p) Γ) :
    (contextFourProof T Γ p t u v s d).val = contextFourCode p.val t.val u.val v.val s.val Γ.val d.val := by
  simp only [contextFourProof,contextFourCode,contextDoubleProof_val,TDerivation.cast_val,
    Semiformula.val_substs,Semiformula.val_all,SemitermVec.q_val_eq_qVec,SemitermVec.val_cons,SemitermVec.val_nil]

#print axioms contextFourGraph_defined
#print axioms contextFourProof
#print axioms contextFourProof_val
end models
end PA194ContextFourSpecializeCode
