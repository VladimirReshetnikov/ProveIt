import PA194TraceSubset
import PA194TraceDirectShift
import PA194TraceDirectMember
import PA194ContextAllCode
import PA194GreatestSuccessorAtCode
import PA194DomainGreatestAtCode
import PA194ContextExsWitnessCode
import PA194FullSepWitnessBranch
import PA194DomainInstances
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PA194MemberNonempty
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceSubset PA194TraceDirectShift PA194TraceDirectMember PA194TraceDirectSyntax PA194ContextAllCode PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def nonemptyTemplate : Semiproposition M6.PA.RelationalSource.language 1 := nonempty (.bvar 0)

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

open M6.PA.RelationalSource

open M6.PA.RelationalSource

noncomputable def nonemptyBody (c : M) : Semiformula M SourceL 1 :=
  Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.fvar c]

theorem nonemptyAt_eq_ex (c : M) :
    ((⌜nonemptyTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c] : Formula M SourceL) = ∃⁰ nonemptyBody c := by
  have hs : nonemptyTemplate = ∃⁰ mem (.bvar 1) (.bvar 0) := by simp [nonemptyTemplate,nonempty]
  rw [hs]
  simp [nonemptyBody,mem,Semiformula.typedQuote,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

theorem nonemptyBody_at (c x : M) :
    (nonemptyBody c).subst ![Semiterm.fvar x] =
      ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) := by
  simp [nonemptyBody]

noncomputable def memberNonemptyProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c x : M)
    (d : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜nonemptyTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ := by
  let body := nonemptyBody c
  let target := insert (∃⁰ body) Γ
  let d' := TDerivation.cast (congrArg (fun f => insert f Γ) (nonemptyBody_at c x).symm) d
  let wd : T ⊢!ᵈᵉʳ insert (body.subst ![Semiterm.fvar x]) target := TDerivation.wk d' (by intro y hy; simp [target] at hy ⊢; tauto)
  let out := TDerivation.exs' (by simp [target]) (Semiterm.fvar x) wd
  exact TDerivation.cast (congrArg (fun f => insert f Γ) (nonemptyAt_eq_ex c).symm) out

noncomputable def nonemptyBodyCode (c : M) : M :=
  ^rel (2 : M) (1 : M) (?[ ^#(0 : M), ^&c] : M)

theorem nonemptyBody_val (c : M) : (nonemptyBody c).val = nonemptyBodyCode c := by
  simp [nonemptyBody,nonemptyBodyCode,SemitermVec.val_succ]
  change ((1 : Nat) : M) = 1
  simp

noncomputable def nonemptyBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out c. ∃ z, !qqBvarDef z 0 ∧ ∃ tc, !qqFvarDef tc c ∧ ∃ v1, !adjoinDef v1 tc 0 ∧
    ∃ vec, !adjoinDef vec z v1 ∧ !qqRelDef out 2 1 vec”

theorem nonemptyBodyGraph_defined : 𝚺₁-Function₁ (nonemptyBodyCode : M → M) via nonemptyBodyGraph := by
  exact .mk fun v => by simp [nonemptyBodyGraph,nonemptyBodyCode]

noncomputable def memberNonemptyCode (c x g d : M) : M :=
  let body := nonemptyBodyCode c
  let target := insert (^∃ body) g
  let wd := wkRule (insert (memberFvarCode x c) target) d
  exsIntro target body (^&x) wd

noncomputable def memberNonemptyGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out c x g d. ∃ body, !nonemptyBodyGraph body c ∧ ∃ ex, !qqExsDef ex body ∧
    ∃ target, !insertDef target ex g ∧ ∃ mem, !memberFvarGraph mem x c ∧
    ∃ wseq, !insertDef wseq mem target ∧ ∃ wd, !wkRuleGraph wd wseq d ∧
    ∃ term, !qqFvarDef term x ∧ !exsIntroGraph out target body term wd”

theorem memberNonemptyGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => memberNonemptyCode (v 0) (v 1) (v 2) (v 3)) memberNonemptyGraph := by
  haveI := nonemptyBodyGraph_defined (M := M)
  haveI := memberFvarGraph_defined (M := M)
  exact .mk fun v => by simp [memberNonemptyGraph,memberNonemptyCode]

@[simp] theorem memberNonemptyProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c x : M)
    (d : T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL) Γ) :
    (memberNonemptyProof T Γ c x d).val = memberNonemptyCode c x Γ.val d.val := by
  have hm : ((Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar c]) : Formula M SourceL).val = memberFvarCode x c := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  have hi : ((nonemptyBody c).subst ![Semiterm.fvar x] : Formula M SourceL).val = memberFvarCode x c := by rw [nonemptyBody_at,hm]
  simp only [memberNonemptyProof,memberNonemptyCode,TDerivation.cast_val,TDerivation.exs'_val,TDerivation.wk_val,
    Sequent.val_insert,Bootstrapping.Semiformula.val_exs,Bootstrapping.Semiterm.fvar_val,nonemptyBody_val,hi]

#print axioms nonemptyBody_val
#print axioms nonemptyBodyGraph_defined
#print axioms memberNonemptyGraph_defined
#print axioms memberNonemptyProof_val
#print axioms nonemptyAt_eq_ex
#print axioms nonemptyBody_at
#print axioms memberNonemptyProof
end models
end PA194MemberNonempty
