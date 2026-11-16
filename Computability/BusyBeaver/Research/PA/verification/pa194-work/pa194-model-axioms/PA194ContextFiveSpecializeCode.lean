import PA194ContextTripleSpecializeCode
import PA194ContextDoubleSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextFiveSpecializeCode
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

noncomputable def contextFiveCode (p t u v s r g d : M) : M :=
  let vec := (?[s,r] : M)
  let q1 := qVec SourceL vec
  let q2 := qVec SourceL q1
  let q3 := qVec SourceL q2
  let three := subst SourceL q3 p
  let first := contextDoubleCode (^∀ (^∀ (^∀ p))) s r g d
  contextTripleCode three t u v g first

noncomputable def contextFiveGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out p t u v s r g d. ∃ rvec, !adjoinDef rvec r 0 ∧ ∃ vec, !adjoinDef vec s rvec ∧
    ∃ q1, !(qVecGraph SourceL) q1 vec ∧ ∃ q2, !(qVecGraph SourceL) q2 q1 ∧
    ∃ q3, !(qVecGraph SourceL) q3 q2 ∧ ∃ three, !(substsGraph SourceL) three q3 p ∧
    ∃ a1, !qqAllDef a1 p ∧ ∃ a2, !qqAllDef a2 a1 ∧ ∃ a3, !qqAllDef a3 a2 ∧
    ∃ first, !contextDoubleGraph first a3 s r g d ∧ !contextTripleGraph out three t u v g first”

theorem contextFiveGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 8 → M => contextFiveCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) contextFiveGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextTripleGraph_defined (M := M)
  exact .mk fun w => by simp [contextFiveGraph,contextFiveCode]

noncomputable def contextFiveProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 5) (t u v s r : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u,v,s,r]) Γ := by
  let first := contextDoubleProof T Γ (∀⁰ ∀⁰ ∀⁰ p) s r d
  have he1 : (∀⁰ ∀⁰ ∀⁰ p).subst ![s,r] = ∀⁰ ∀⁰ ∀⁰ p.subst (SemitermVec.q (SemitermVec.q (SemitermVec.q ![s,r]))) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let rest := contextTripleProof T Γ (p.subst (SemitermVec.q (SemitermVec.q (SemitermVec.q ![s,r])))) t u v first'
  have he2 : (p.subst (SemitermVec.q (SemitermVec.q (SemitermVec.q ![s,r])))).subst ![t,u,v] = p.subst ![t,u,v,s,r] := by
    simp [Semiformula.substs_substs, Semiterm.bShift_substs_succ]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) rest

@[simp] theorem contextFiveProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 5) (t u v s r : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ p) Γ) :
    (contextFiveProof T Γ p t u v s r d).val = contextFiveCode p.val t.val u.val v.val s.val r.val Γ.val d.val := by
  simp only [contextFiveProof,contextFiveCode,contextTripleProof_val,contextDoubleProof_val,
    TDerivation.cast_val,Semiformula.val_substs,Semiformula.val_all,SemitermVec.q_val_eq_qVec,
    SemitermVec.val_cons,SemitermVec.val_nil]


#print axioms contextFiveGraph_defined
#print axioms contextFiveProof
#print axioms contextFiveProof_val
end models
end PA194ContextFiveSpecializeCode
