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
import PA194IsoSuccessorSuppliers
import PA194FixedInstanceShift
import PA194IsoGuardAt
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
namespace PA194IsoGuardOpen
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


theorem isoGuardBody_open (c a : M) (hc : IsSemiformula SourceL 1 c) :
    ((∼((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.fvar a]) ⋎
       (⟨c,by simpa using hc⟩ : Semiformula M SourceL 1)).free) =
    (∼((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (a+1)]) ⋎
       ((⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar 0])) := by
  have hf : (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).shift = ⌜isoGuardTemplate⌝ := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed isoGuardTemplate (by decide)
  have hcshift : (⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).shift =
      (⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1) := by
    apply Semiformula.ext
    rfl
  simp [Bootstrapping.Semiformula.free,Semiformula.shift_substs,Semiformula.substs_substs,hf,hcshift]

theorem matchSuccessor_ignore_middle (a b p t : M) :
    ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : Formula M SourceL) =
      (⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar t,Semiterm.fvar p] := by
  have hs : matchSuccessorBound3 = successorTemplate ⇜ ![#0,#2] := by
    simp only [matchSuccessorBound3,successorTemplate]
    ordinalSyntax
  have ht : (⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3) =
      (⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.bvar 2] := by
    rw [hs,Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

open PA194FixedInstanceShift PA194IsoSuccessorSuppliers PA194IsoGuardShift PA194IsoGuardAt

noncomputable def isoGuardSuccessorProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a p : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar p]) Γ)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode c,stepCode_scoped c hc⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let guard : Formula M SourceL := (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (a+1)]
  let prop : Formula M SourceL := (⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar 0]
  let branch : Sequent M SourceL := insert (∼guard) Γ.shift
  have hweak {r : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert r Γ.shift) : T ⊢!ᵈᵉʳ insert r branch :=
    TDerivation.wk d (by intro x hx; simp [branch] at hx ⊢; tauto)
  let u : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝
  have hu : u.shift = u := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed (∀⁰ ∀⁰ ∀⁰ isoMatchBound) (by decide)
  let du' := hweak (TDerivation.cast (congrArg (fun z => insert z Γ.shift) hu) (contextShiftProof T Γ u du))
  let rel : Semiformula M SourceL 3 := ⌜matchSuccessorBound3⌝
  have hf : rel.shift = rel := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed matchSuccessorBound3 (by decide)
  let ds0 := fixedThreeShiftProof T Γ rel hf a 0 p ds
  have he : (rel.subst ![Semiterm.fvar (a+1),Semiterm.fvar (0+1),Semiterm.fvar (p+1)] : Formula M SourceL) =
      rel.subst ![Semiterm.fvar (a+1),Semiterm.fvar 0,Semiterm.fvar (p+1)] := matchSuccessor_ignore_middle (a+1) (0+1) (p+1) 0
  let ds' := hweak (TDerivation.cast (congrArg (fun z => insert z Γ.shift) he) ds0)
  let dq' := hweak (isoGuardShiftProof T Γ c p hc dq)
  let hstep' := hweak (contextualStepShiftProof T Γ c hc hstep)
  let dg : T ⊢!ᵈᵉʳ insert guard branch := TDerivation.em guard (by simp [branch]) (by simp [branch])
  let dp := isoSuccessorSuppliedProof T branch (shift SourceL c) (a+1) 0 (p+1) hc.shift du' ds' dg dq' hstep'
  let target : Sequent M SourceL := insert (∼guard ⋎ prop) Γ.shift
  let wd : T ⊢!ᵈᵉʳ insert (∼guard) (insert prop target) :=
    TDerivation.wk dp (by intro x hx; simp [branch,target] at hx ⊢; tauto)
  let dor : T ⊢!ᵈᵉʳ target := TDerivation.or' (by simp [target]) wd
  let dbody := TDerivation.cast (congrArg (fun z => insert z Γ.shift) (isoGuardBody_open c a hc).symm) dor
  exact isoGuardIntroProof T Γ c a hc dbody

noncomputable def isoGuardSuccessorCode (c a p ctx du ds dq hstep : M) : M :=
  let u := (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : M)
  let succTemplate := (⌜matchSuccessorBound3⌝ : M)
  let succ := subst SourceL (?[ ^&a, ^&(0 : M), ^&p]) succTemplate
  let guard := subst SourceL (?[ ^&(0 : M), ^&(a+1)]) (⌜isoGuardTemplate⌝ : M)
  let ng := neg SourceL guard
  let shiftedCtx := setShift SourceL ctx
  let branch := insert ng shiftedCtx
  let cp := shift SourceL c
  let du' := wkRule (insert u branch) (contextShiftCode u ctx du)
  let succ' := subst SourceL (?[ ^&(a+1), ^&(0 : M), ^&(p+1)]) succTemplate
  let ds' := wkRule (insert succ' branch) (contextShiftCode succ ctx ds)
  let qprop := substs1 SourceL (^&(p+1)) (isoGuardProperty cp)
  let dq' := wkRule (insert qprop branch) (isoGuardShiftCode c p ctx dq)
  let step' := stepCode cp
  let hstep' := wkRule (insert step' branch) (contextShiftCode (stepCode c) ctx hstep)
  let dg := axL (insert guard branch) guard
  let dp := isoSuccessorSuppliedCode cp (a+1) 0 (p+1) branch du' ds' dg dq' hstep'
  let prop := substs1 SourceL (^&(0 : M)) cp
  let target := insert (ng ^⋎ prop) shiftedCtx
  let wd := wkRule (insert ng (insert prop target)) dp
  let dor := orIntro target ng prop wd
  isoGuardIntroCode c a ctx dor

@[simp] theorem isoGuardSuccessorProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a p : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar p]) Γ)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode c,stepCode_scoped c hc⟩ : Formula M SourceL) Γ) :
    (isoGuardSuccessorProof T Γ c a p hc du ds dq hstep).val = isoGuardSuccessorCode c a p Γ.val du.val ds.val dq.val hstep.val := by
  simp [isoGuardSuccessorProof,isoGuardSuccessorCode,Semiformula.quote_def,SemitermVec.val_succ,substs1,Sequent.shift]

noncomputable def isoGuardSuccessorGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out c a p ctx du ds dq hstep.
    ∃ u, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)) u ∧
    ∃ st, !(fixedFormulaQuoteGraph matchSuccessorBound3) st ∧ ∃ gt, !(fixedFormulaQuoteGraph isoGuardTemplate) gt ∧
    ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧ ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧ ∃ rt, !(fixedFormulaQuoteGraph successorTemplate) rt ∧
    ∃ nextA, nextA = a + 1 ∧ ∃ nextP, nextP = p + 1 ∧
    ∃ fa, !qqFvarDef fa a ∧ ∃ fp, !qqFvarDef fp p ∧ ∃ fzero, !qqFvarDef fzero 0 ∧ ∃ fna, !qqFvarDef fna nextA ∧ ∃ fnp, !qqFvarDef fnp nextP ∧
    ∃ vp, !adjoinDef vp fp 0 ∧ ∃ v0p, !adjoinDef v0p fzero vp ∧ ∃ vec, !adjoinDef vec fa v0p ∧
    ∃ succ, !(substsGraph SourceL) succ vec st ∧ ∃ vnp, !adjoinDef vnp fnp 0 ∧ ∃ v0np, !adjoinDef v0np fzero vnp ∧
    ∃ vecNext, !adjoinDef vecNext fna v0np ∧ ∃ succNext, !(substsGraph SourceL) succNext vecNext st ∧
    ∃ vna, !adjoinDef vna fna 0 ∧ ∃ gvec, !adjoinDef gvec fzero vna ∧ ∃ guard, !(substsGraph SourceL) guard gvec gt ∧
    ∃ ng, !(negGraph SourceL) ng guard ∧ ∃ shiftedCtx, !(setShiftGraph SourceL) shiftedCtx ctx ∧ ∃ branch, !insertDef branch ng shiftedCtx ∧
    ∃ cp, !(shiftGraph SourceL) cp c ∧ ∃ ush, !contextShiftGraph ush u ctx du ∧ ∃ us, !insertDef us u branch ∧ ∃ du', !wkRuleGraph du' us ush ∧
    ∃ ssh, !contextShiftGraph ssh succ ctx ds ∧ ∃ ss, !insertDef ss succNext branch ∧ ∃ ds', !wkRuleGraph ds' ss ssh ∧
    ∃ q, !isoGuardPropertyGraph q cp ∧ ∃ qprop, !(substs1Graph SourceL) qprop fnp q ∧ ∃ qsh, !isoGuardShiftGraph qsh c p ctx dq ∧
    ∃ qs, !insertDef qs qprop branch ∧ ∃ dq', !wkRuleGraph dq' qs qsh ∧
    ∃ step0, !ordinalStepFromPropertyGraph step0 d1 d0 rt c ∧ ∃ step1, !ordinalStepFromPropertyGraph step1 d1 d0 rt cp ∧
    ∃ hsh, !contextShiftGraph hsh step0 ctx hstep ∧ ∃ hs, !insertDef hs step1 branch ∧ ∃ hstep', !wkRuleGraph hstep' hs hsh ∧
    ∃ gs, !insertDef gs guard branch ∧ ∃ dg, !axLGraph dg gs guard ∧
    ∃ dp, !isoSuccessorSuppliedGraph dp cp nextA 0 nextP branch du' ds' dg dq' hstep' ∧
    ∃ prop, !(substs1Graph SourceL) prop fzero cp ∧ ∃ imp, !qqOrDef imp ng prop ∧ ∃ target, !insertDef target imp shiftedCtx ∧
    ∃ pp, !insertDef pp prop target ∧ ∃ premise, !insertDef premise ng pp ∧ ∃ wd, !wkRuleGraph wd premise dp ∧
    ∃ dor, !orIntroGraph dor target ng prop wd ∧ !isoGuardIntroGraph out c a ctx dor”

theorem isoGuardSuccessorGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 8 → M => isoGuardSuccessorCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) isoGuardSuccessorGraph := by
  haveI := ordinalStepFromPropertyGraph_defined (M := M)
  haveI := isoGuardPropertyGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := isoGuardShiftGraph_defined (M := M)
  haveI := isoSuccessorSuppliedGraph_defined (M := M)
  haveI := isoGuardIntroGraph_defined (M := M)
  exact .mk fun w => by simp [isoGuardSuccessorGraph,isoGuardSuccessorCode,stepCode,fixedFormulaQuoteGraph_correct]

#print axioms isoGuardSuccessorGraph_defined
#print axioms isoGuardSuccessorProof_val
#print axioms isoGuardSuccessorProof
#print axioms isoGuardBody_open
#print axioms matchSuccessor_ignore_middle
end models
end PA194IsoGuardOpen
