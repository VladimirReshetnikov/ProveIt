import PA194MemberDomainClosedModel
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194MemberDomainAtCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194MemberDomainClosedModel PA194MemberDomainClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

open M6.PA.RelationalSource

open M6.PA.RelationalSource

noncomputable def memberDomainAtCode (a b g du hd hm : M) : M :=
  let d1 := (⌜domainOne⌝ : M)
  let d0 := (⌜domainZero⌝ : M)
  let body := (⌜memberDomainBound⌝ : M)
  let vec := (?[ ^&b, ^&a] : M)
  let id1 := subst SourceL vec d1
  let id0 := subst SourceL vec d0
  let mem := memberFvarCode b a
  let sp := contextDoubleCode body (^&b) (^&a) g du
  let mid := contextMPCode id1 (neg SourceL mem ^⋎ id0) g sp hd
  contextMPCode mem id0 g mid hm

noncomputable def memberDomainAtGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out a b g du hd hm. ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧
    ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧ ∃ body, !(fixedFormulaQuoteGraph memberDomainBound) body ∧
    ∃ tb, !qqFvarDef tb b ∧ ∃ ta, !qqFvarDef ta a ∧ ∃ tail, !adjoinDef tail ta 0 ∧ ∃ vec, !adjoinDef vec tb tail ∧
    ∃ id1, !(substsGraph SourceL) id1 vec d1 ∧ ∃ id0, !(substsGraph SourceL) id0 vec d0 ∧
    ∃ mem, !memberFvarGraph mem b a ∧ ∃ nm, !(negGraph SourceL) nm mem ∧ ∃ imp, !qqOrDef imp nm id0 ∧
    ∃ sp, !contextDoubleGraph sp body tb ta g du ∧ ∃ mid, !contextMPGraph mid id1 imp g sp hd ∧
    !contextMPGraph out mem id0 g mid hm”

theorem memberDomainAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => memberDomainAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) memberDomainAtGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [memberDomainAtGraph,memberDomainAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def memberDomainAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ := by
  let body : Semiformula M SourceL 2 := ⌜memberDomainBound⌝
  let d1 : Semiformula M SourceL 2 := ⌜domainOne⌝
  let d0 : Semiformula M SourceL 2 := ⌜domainZero⌝
  let mem : Semiformula M SourceL 2 := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.bvar 1]
  have heb : body = d1 🡒 (mem 🡒 d0) := by
    simp [body,d1,d0,mem,memberDomainBound]
    congr 1
    funext i
    fin_cases i <;> simp
  have heu : (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ body := by
    simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextDoubleProof T Γ body (Semiterm.fvar b) (Semiterm.fvar a) du'
  have hei : (body.subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      ((d1.subst ![Semiterm.fvar b,Semiterm.fvar a]) 🡒
       ((mem.subst ![Semiterm.fvar b,Semiterm.fvar a]) 🡒 (d0.subst ![Semiterm.fvar b,Semiterm.fvar a]))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  let mid := contextMPProof T Γ _ _ sp' hd
  have hem : mem.subst ![Semiterm.fvar b,Semiterm.fvar a] =
      (Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) := by
    simp [mem]
  let hm' := TDerivation.cast (congrArg (fun q => insert q Γ) hem.symm) hm
  exact contextMPProof T Γ _ _ mid hm'

@[simp] theorem memberDomainAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL) Γ) :
    (memberDomainAtProof T Γ a b du hd hm).val = memberDomainAtCode a b Γ.val du.val hd.val hm.val := by
  have hmem : ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL)).val = memberFvarCode b a := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  have hmemSub : (((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.bvar 1] : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL).val = memberFvarCode b a := by
    have he : (Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.bvar 1] : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] =
        (Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) := by simp
    rw [he]
    exact hmem
  simp only [memberDomainAtProof,memberDomainAtCode,contextMPProof_val,contextDoubleProof_val,TDerivation.cast_val,
    Bootstrapping.Semiformula.imp_def,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,
    hmemSub,Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiterm.fvar_val,SemitermVec.val_succ,hmem]
  simp [Matrix.vecHead,Matrix.vecTail,Semiformula.quote_def]

/-- Member-domain application with the fixed logical theorem supplied internally. -/
noncomputable def memberDomainAtFromLogic (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ := by
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : T ⊢!ᵈᵉʳ insert uq Γ := TDerivation.wk (memberDomainUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  exact memberDomainAtProof T Γ a b du hd hm

#print axioms memberDomainAtProof_val
#print axioms memberDomainAtFromLogic
#print axioms memberDomainAtGraph_defined
#print axioms memberDomainAtProof
end models
end PA194MemberDomainAtCode
