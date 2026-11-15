import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194IsoWitnessComponents
import PA194IsoWitnessBranch
import PA194OrdinalStepApplicationCode
import PA194IsoWitnessStepComponents
import PA194IsoGuardMatch
import PA194IsoSuccessorProperty
import PA194DomainInstances
import PA194BadTraceStepShift
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoSuccessorSuppliers
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

open PA194InductionStepShiftCode PA194IsoWitnessComponents PA194OrdinalStepQuote PA194InternalOrdinalStep PA194OrdinalStepApplicationCode PA194IsoWitnessBranch

open PA194IsoWitnessStepComponents PA194IsoGuardMatch

open PA194OrdinalStepFromProperty PA194IsoSuccessorProperty PA194DomainInstances PA194OrdinalBaseQuote PA194BadTraceStepShift

theorem matchDomainOne (a b p : M) :
    ((⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : Formula M SourceL) =
      (⌜domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b] := by
  have hs : matchDomainBound3 = domainTemplate ⇜ ![#1] := by
    simp only [matchDomainBound3,domainTemplate]
    ordinalSyntax
  have ht : (⌜matchDomainBound3⌝ : Semiformula M SourceL 3) =
      (⌜domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 1] := by
    rw [hs,Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

theorem matchDomainShift (a b p : M) :
    ((⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : Formula M SourceL).shift =
      (⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0] := by
  rw [matchDomainOne a b p,domainZeroAt 0 (b+1)]
  have hf : (⌜domainTemplate⌝ : Semiformula M SourceL 1).shift = ⌜domainTemplate⌝ := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed domainTemplate (by decide)
  simp [Semiformula.shift_substs,hf]

noncomputable def isoSuccessorSuppliedCode (c a b p ctx du ds dg dq hstep : M) : M :=
  let vec := (?[ ^&a, ^&b, ^&p] : M)
  let dom := subst SourceL vec (⌜matchDomainBound3⌝ : M)
  let iso := subst SourceL vec (⌜matchIsoBound3⌝ : M)
  let dd := contextAndLeftCode dom iso ctx dg
  let dshift := contextShiftCode dom ctx dd
  let wvec := (?[ ^#(0 : M), ^&a, ^&b, ^&p] : M)
  let witness := free SourceL (subst SourceL wvec (⌜matchWitnessBody4⌝ : M))
  let branch := insert (neg SourceL witness) (setShift SourceL ctx)
  let target := wkRule (insert (shift SourceL dom) branch) dshift
  let stepShift := contextShiftCode (stepCode c) ctx hstep
  let stepBranch := wkRule (insert (stepCode (shift SourceL c)) branch) stepShift
  isoSuccessorPropertyCode c a b p ctx du ds dg dq stepBranch target

noncomputable def isoSuccessorSuppliedGraph : 𝚺₁.Semisentence 11 := .mkSigma
  “out c a b p ctx du ds dg dq hstep.
    ∃ dt, !(fixedFormulaQuoteGraph matchDomainBound3) dt ∧ ∃ it, !(fixedFormulaQuoteGraph matchIsoBound3) it ∧
    ∃ wt, !(fixedFormulaQuoteGraph matchWitnessBody4) wt ∧
    ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧ ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧ ∃ st, !(fixedFormulaQuoteGraph successorTemplate) st ∧
    ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧ ∃ zero, !qqBvarDef zero 0 ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ vec, !adjoinDef vec va v2 ∧ ∃ wvec, !adjoinDef wvec zero vec ∧
    ∃ dom, !(substsGraph SourceL) dom vec dt ∧ ∃ iso, !(substsGraph SourceL) iso vec it ∧
    ∃ dd, !contextAndLeftGraph dd dom iso ctx dg ∧ ∃ dshift, !contextShiftGraph dshift dom ctx dd ∧
    ∃ wb, !(substsGraph SourceL) wb wvec wt ∧ ∃ witness, !(freeGraph SourceL) witness wb ∧ ∃ nw, !(negGraph SourceL) nw witness ∧
    ∃ ctxShift, !(setShiftGraph SourceL) ctxShift ctx ∧ ∃ branch, !insertDef branch nw ctxShift ∧
    ∃ domShift, !(shiftGraph SourceL) domShift dom ∧ ∃ targetS, !insertDef targetS domShift branch ∧ ∃ target, !wkRuleGraph target targetS dshift ∧
    ∃ step, !ordinalStepFromPropertyGraph step d1 d0 st c ∧ ∃ stepShift, !contextShiftGraph stepShift step ctx hstep ∧
    ∃ cp, !(shiftGraph SourceL) cp c ∧ ∃ newStep, !ordinalStepFromPropertyGraph newStep d1 d0 st cp ∧
    ∃ stepS, !insertDef stepS newStep branch ∧ ∃ stepBranch, !wkRuleGraph stepBranch stepS stepShift ∧
    !isoSuccessorPropertyGraph out c a b p ctx du ds dg dq stepBranch target”

theorem isoSuccessorSuppliedGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 10 → M => isoSuccessorSuppliedCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)) isoSuccessorSuppliedGraph := by
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := isoSuccessorPropertyGraph_defined (M := M)
  exact .mk fun w => by simp [isoSuccessorSuppliedGraph,isoSuccessorSuppliedCode,stepCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoSuccessorSuppliedProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode c,stepCode_scoped c hc⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let dom : Formula M SourceL := (⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]
  let iso : Formula M SourceL := (⌜matchIsoBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]
  let witness : Formula M SourceL := ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let branch : Sequent M SourceL := insert (∼witness) Γ.shift
  let dg' := TDerivation.cast (congrArg (fun z => insert z Γ) (isoGuard_match_components a b p)) dg
  let dd := contextAndLeftProof T Γ dom iso dg'
  let dshift := contextShiftProof T Γ dom dd
  let dt : T ⊢!ᵈᵉʳ insert dom.shift branch := TDerivation.wk dshift (by intro x hx; simp [branch] at hx ⊢; tauto)
  let target := TDerivation.cast (congrArg (fun z => insert z branch) (matchDomainShift a b p)) dt
  let stepShift := contextualStepShiftProof T Γ c hc hstep
  let stepBranch : T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL c),stepCode_scoped _ hc.shift⟩ : Formula M SourceL) branch :=
    TDerivation.wk stepShift (by intro x hx; simp [branch] at hx ⊢; tauto)
  exact isoSuccessorPropertyProof T Γ c a b p hc du ds dg dq stepBranch target

@[simp] theorem isoSuccessorSuppliedProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode c,stepCode_scoped c hc⟩ : Formula M SourceL) Γ) :
    (isoSuccessorSuppliedProof T Γ c a b p hc du ds dg dq hstep).val = isoSuccessorSuppliedCode c a b p Γ.val du.val ds.val dg.val dq.val hstep.val := by
  simp [isoSuccessorSuppliedProof,isoSuccessorSuppliedCode,Semiformula.quote_def,SemitermVec.val_succ,Sequent.shift]

#print axioms isoSuccessorSuppliedGraph_defined
#print axioms isoSuccessorSuppliedProof
#print axioms isoSuccessorSuppliedProof_val
#print axioms matchDomainOne
#print axioms matchDomainShift
end models
end PA194IsoSuccessorSuppliers
