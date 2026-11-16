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
import PA194OrderIsoZeroModel
import PA194IsoZeroAt
import PA194IsoGuardOpen
import PA194OrdinalBaseApplicationCode
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
namespace PA194IsoGuardZero
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


open PA194OrderIsoZeroModel PA194OrdinalBaseApplicationCode PA194OrdinalBaseQuote PA194InternalOrdinalBase PA194InductionBaseShiftCode PA194ContextDoubleSpecializeCode M6.PA.RelationalSource.PairGraph

open PA194IsoZeroAt PA194IsoGuardOpen PA194FixedInstanceShift PA194ContextualBaseShift PA194IsoGuardAt

noncomputable def isoGuardZeroProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜zeroIsoStatement⌝ : Formula M SourceL) Γ)
    (dz : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode c,inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hc⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let guard : Formula M SourceL := (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (a+1)]
  let prop : Formula M SourceL := (⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar 0]
  let branch : Sequent M SourceL := insert (∼guard) Γ.shift
  have hweak {r : Formula M SourceL} (d : T ⊢!ᵈᵉʳ insert r Γ.shift) : T ⊢!ᵈᵉʳ insert r branch :=
    TDerivation.wk d (by intro x hx; simp [branch] at hx ⊢; tauto)
  let u : Formula M SourceL := ⌜zeroIsoStatement⌝
  have hu : u.shift = u := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed zeroIsoStatement (by decide)
  let du' := hweak (TDerivation.cast (congrArg (fun z => insert z Γ.shift) hu) (contextShiftProof T Γ u du))
  let Z : Semiformula M SourceL 1 := ⌜zeroTemplate⌝
  have hz : Z.shift = Z := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed zeroTemplate (by decide)
  let dz' := hweak (fixedOneShiftProof T Γ Z hz a dz)
  let hb' := hweak (contextualBaseShiftProof T Γ c hc hb)
  let dg : T ⊢!ᵈᵉʳ insert guard branch := TDerivation.em guard (by simp [branch]) (by simp [branch])
  let dp := isoZeroAtProof T branch (shift SourceL c) (a+1) 0 hc.shift du' dz' dg hb'
  let target : Sequent M SourceL := insert (∼guard ⋎ prop) Γ.shift
  let wd : T ⊢!ᵈᵉʳ insert (∼guard) (insert prop target) :=
    TDerivation.wk dp (by intro x hx; simp [branch,target] at hx ⊢; tauto)
  let dor : T ⊢!ᵈᵉʳ target := TDerivation.or' (by simp [target]) wd
  let dbody := TDerivation.cast (congrArg (fun z => insert z Γ.shift) (isoGuardBody_open c a hc).symm) dor
  exact isoGuardIntroProof T Γ c a hc dbody

noncomputable def isoGuardZeroCode (c a ctx du dz hb : M) : M :=
  let u := (⌜zeroIsoStatement⌝ : M)
  let z := (⌜zeroTemplate⌝ : M)
  let za := substs1 SourceL (^&a) z
  let guard := subst SourceL (?[ ^&(0 : M), ^&(a+1)]) (⌜isoGuardTemplate⌝ : M)
  let ng := neg SourceL guard
  let shiftedCtx := setShift SourceL ctx
  let branch := insert ng shiftedCtx
  let cp := shift SourceL c
  let du' := wkRule (insert u branch) (contextShiftCode u ctx du)
  let znext := substs1 SourceL (^&(a+1)) z
  let dz' := wkRule (insert znext branch) (contextShiftCode za ctx dz)
  let hb' := wkRule (insert (baseCode cp) branch) (contextShiftCode (baseCode c) ctx hb)
  let dg := axL (insert guard branch) guard
  let dp := isoZeroAtCode cp (a+1) 0 branch du' dz' dg hb'
  let prop := substs1 SourceL (^&(0 : M)) cp
  let target := insert (ng ^⋎ prop) shiftedCtx
  let wd := wkRule (insert ng (insert prop target)) dp
  let dor := orIntro target ng prop wd
  isoGuardIntroCode c a ctx dor

noncomputable def isoGuardZeroGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out c a ctx du dz hb.
    ∃ u, !(fixedFormulaQuoteGraph zeroIsoStatement) u ∧ ∃ z, !(fixedFormulaQuoteGraph zeroTemplate) z ∧
    ∃ dt, !(fixedFormulaQuoteGraph domainTemplate) dt ∧ ∃ gt, !(fixedFormulaQuoteGraph isoGuardTemplate) gt ∧
    ∃ nextA, nextA = a + 1 ∧ ∃ fa, !qqFvarDef fa a ∧ ∃ fzero, !qqFvarDef fzero 0 ∧ ∃ fna, !qqFvarDef fna nextA ∧
    ∃ za, !(substs1Graph SourceL) za fa z ∧ ∃ znext, !(substs1Graph SourceL) znext fna z ∧
    ∃ vna, !adjoinDef vna fna 0 ∧ ∃ gvec, !adjoinDef gvec fzero vna ∧ ∃ guard, !(substsGraph SourceL) guard gvec gt ∧
    ∃ ng, !(negGraph SourceL) ng guard ∧ ∃ shiftedCtx, !(setShiftGraph SourceL) shiftedCtx ctx ∧ ∃ branch, !insertDef branch ng shiftedCtx ∧
    ∃ cp, !(shiftGraph SourceL) cp c ∧ ∃ ush, !contextShiftGraph ush u ctx du ∧ ∃ us, !insertDef us u branch ∧ ∃ du', !wkRuleGraph du' us ush ∧
    ∃ zsh, !contextShiftGraph zsh za ctx dz ∧ ∃ zs, !insertDef zs znext branch ∧ ∃ dz', !wkRuleGraph dz' zs zsh ∧
    ∃ base0, !inductionBaseGraph base0 dt z c ∧ ∃ base1, !inductionBaseGraph base1 dt z cp ∧
    ∃ bsh, !contextShiftGraph bsh base0 ctx hb ∧ ∃ bs, !insertDef bs base1 branch ∧ ∃ hb', !wkRuleGraph hb' bs bsh ∧
    ∃ gs, !insertDef gs guard branch ∧ ∃ dg, !axLGraph dg gs guard ∧ ∃ dp, !isoZeroAtGraph dp cp nextA 0 branch du' dz' dg hb' ∧
    ∃ prop, !(substs1Graph SourceL) prop fzero cp ∧ ∃ imp, !qqOrDef imp ng prop ∧ ∃ target, !insertDef target imp shiftedCtx ∧
    ∃ pp, !insertDef pp prop target ∧ ∃ premise, !insertDef premise ng pp ∧ ∃ wd, !wkRuleGraph wd premise dp ∧
    ∃ dor, !orIntroGraph dor target ng prop wd ∧ !isoGuardIntroGraph out c a ctx dor”

theorem isoGuardZeroGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 6 → M => isoGuardZeroCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)) isoGuardZeroGraph := by
  haveI := inductionBaseGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := isoZeroAtGraph_defined (M := M)
  haveI := isoGuardIntroGraph_defined (M := M)
  exact .mk fun w => by simp [isoGuardZeroGraph,isoGuardZeroCode,baseCode,fixedFormulaQuoteGraph_correct]

@[simp] theorem isoGuardZeroProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜zeroIsoStatement⌝ : Formula M SourceL) Γ)
    (dz : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode c,inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hc⟩ : Formula M SourceL) Γ) :
    (isoGuardZeroProof T Γ c a hc du dz hb).val = isoGuardZeroCode c a Γ.val du.val dz.val hb.val := by
  simp [isoGuardZeroProof,isoGuardZeroCode,Semiformula.quote_def,SemitermVec.val_succ,substs1,Sequent.shift]

#print axioms isoGuardZeroGraph_defined
#print axioms isoGuardZeroProof_val
#print axioms isoGuardZeroProof
end models
end PA194IsoGuardZero
