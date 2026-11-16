import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194IsoWitnessComponents
import PA194IsoGuardAt
import PA194IsoWitnessProperty
import PA194IsoGuardShift
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoWitnessBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IsoMatchTemplate PA194ContextAllCode PA194FixedSyntaxQuote PA194IsoGuardProperty PA194TraceDirectSyntax PA194TracePropertyCompose PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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


open PA194ContextAndProjectionCode PA194IsoMatchAtCode M6.PA.RelationalSource.PairGraph

open PA194ContextAndProjectionCode PA194IsoMatchWitness

open PA194IsoWitnessComponents PA194IsoGuardAt PA194IsoWitnessProperty PA194IsoGuardShift

noncomputable def isoWitnessBranchCode (c a b p ctx dq : M) : M :=
  let vec := (?[ ^#(0 : M), ^&a, ^&b, ^&p] : M)
  let witness := free SourceL (subst SourceL vec (⌜matchWitnessBody4⌝ : M))
  let branch := insert (neg SourceL witness) (setShift SourceL ctx)
  let cp := shift SourceL c
  let qp := substs1 SourceL (^&(p+1)) (isoGuardProperty cp)
  let dq' := wkRule (insert qp branch) (isoGuardShiftCode c p ctx dq)
  let dw := axL (insert witness branch) witness
  isoWitnessPropertyCode cp a b p branch dq' dw

noncomputable def isoWitnessBranchGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out c a b p ctx dq. ∃ tmpl, !(fixedFormulaQuoteGraph matchWitnessBody4) tmpl ∧
    ∃ zero, !qqBvarDef zero 0 ∧ ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ v3, !adjoinDef v3 va v2 ∧ ∃ vec, !adjoinDef vec zero v3 ∧
    ∃ body, !(substsGraph SourceL) body vec tmpl ∧ ∃ witness, !(freeGraph SourceL) witness body ∧
    ∃ nw, !(negGraph SourceL) nw witness ∧ ∃ shiftedCtx, !(setShiftGraph SourceL) shiftedCtx ctx ∧ ∃ branch, !insertDef branch nw shiftedCtx ∧
    ∃ cp, !(shiftGraph SourceL) cp c ∧ ∃ q, !isoGuardPropertyGraph q cp ∧ ∃ next, next = p + 1 ∧ ∃ t, !qqFvarDef t next ∧
    ∃ qp, !(substs1Graph SourceL) qp t q ∧ ∃ shifted, !isoGuardShiftGraph shifted c p ctx dq ∧ ∃ qbranch, !insertDef qbranch qp branch ∧
    ∃ dq', !wkRuleGraph dq' qbranch shifted ∧ ∃ wbranch, !insertDef wbranch witness branch ∧ ∃ dw, !axLGraph dw wbranch witness ∧
    !isoWitnessPropertyGraph out cp a b p branch dq' dw”

theorem isoWitnessBranchGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 6 → M => isoWitnessBranchCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)) isoWitnessBranchGraph := by
  haveI := isoGuardPropertyGraph_defined (M := M)
  haveI := isoGuardShiftGraph_defined (M := M)
  haveI := isoWitnessPropertyGraph_defined (M := M)
  exact .mk fun w => by simp [isoWitnessBranchGraph,isoWitnessBranchCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoWitnessBranchProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar 0])
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
        ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift) := by
  let witness : Formula M SourceL := ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let branch : Sequent M SourceL := insert (∼witness) Γ.shift
  let ds := isoGuardShiftProof T Γ c p hc dq
  let dq' : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty (shift SourceL c),by simpa using isoGuardProperty_scoped (shift SourceL c) hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (p+1)]) branch :=
    TDerivation.wk ds (by intro x hx; simp [branch] at hx ⊢; tauto)
  let dw : T ⊢!ᵈᵉʳ insert witness branch := TDerivation.em witness (by simp [branch]) (by simp [branch])
  exact isoWitnessPropertyProof T branch (shift SourceL c) a b p hc.shift dq' dw

@[simp] theorem isoWitnessBranchProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ) :
    (isoWitnessBranchProof T Γ c a b p hc dq).val = isoWitnessBranchCode c a b p Γ.val dq.val := by
  simp [isoWitnessBranchProof,isoWitnessBranchCode,Semiformula.quote_def,SemitermVec.val_succ,substs1,Sequent.shift]

#print axioms isoWitnessBranchGraph_defined
#print axioms isoWitnessBranchProof
#print axioms isoWitnessBranchProof_val
end models
end PA194IsoWitnessBranch
