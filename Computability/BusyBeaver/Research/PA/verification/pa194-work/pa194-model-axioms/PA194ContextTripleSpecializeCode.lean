import PA194ContextDoubleSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextTripleSpecializeCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextDoubleSpecializeCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Uniform proof-code composition for three universal instantiations. -/
noncomputable def contextTripleCode (p t u v g d : M) : M :=
  let two := subst SourceL (qVec SourceL (qVec SourceL (?[v] : M))) p
  let first := contextSpecializeCode (^∀ (^∀ p)) v g d
  contextDoubleCode two t u g first

noncomputable def contextTripleGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p t u v g d. ∃ vec, !adjoinDef vec v 0 ∧ ∃ q1, !(qVecGraph SourceL) q1 vec ∧
    ∃ q2, !(qVecGraph SourceL) q2 q1 ∧ ∃ two, !(substsGraph SourceL) two q2 p ∧
    ∃ all1, !qqAllDef all1 p ∧ ∃ all2, !qqAllDef all2 all1 ∧
    ∃ first, !contextSpecializeGraph first all2 v g d ∧ !contextDoubleGraph out two t u g first”

theorem contextTripleGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => contextTripleCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) contextTripleGraph := by
  haveI := contextSpecializeGraph_defined (M := M)
  haveI := contextDoubleGraph_defined (M := M)
  exact .mk fun v => by simp [contextTripleGraph,contextTripleCode]

noncomputable def contextTripleProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 3) (t u v : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ p) Γ) : T ⊢!ᵈᵉʳ insert (p.subst ![t,u,v]) Γ := by
  let first := contextSpecializeProof T Γ (∀⁰ ∀⁰ p) v d
  have he1 : (∀⁰ ∀⁰ p).subst ![v] = ∀⁰ ∀⁰ p.subst (SemitermVec.q (SemitermVec.q ![v])) := by simp
  let first' := TDerivation.cast (congrArg (fun q => insert q Γ) he1) first
  let rest := contextDoubleProof T Γ (p.subst (SemitermVec.q (SemitermVec.q ![v]))) t u first'
  have he2 : (p.subst (SemitermVec.q (SemitermVec.q ![v]))).subst ![t,u] = p.subst ![t,u,v] := by
    simp [Semiformula.substs_substs, Semiterm.bShift_substs_succ]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he2) rest

@[simp] theorem contextTripleProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 3) (t u v : Term M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ p) Γ) :
    (contextTripleProof T Γ p t u v d).val = contextTripleCode p.val t.val u.val v.val Γ.val d.val := by
  have hv : IsUTerm SourceL v.val := v.isSemiterm.isUTerm
  have hbs : IsUTerm SourceL (termBShift SourceL v.val) := v.isSemiterm.termBShift.isUTerm
  simp [contextTripleProof,contextTripleCode,SemitermVec.val_succ,qVec,one_add_one_eq_two,hv,hbs]

#print axioms contextTripleGraph_defined
#print axioms contextTripleProof
#print axioms contextTripleProof_val
end models
end PA194ContextTripleSpecializeCode
