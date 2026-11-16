import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194IsoWitnessComponents
import PA194IsoWitnessBranch
import PA194OrdinalStepApplicationCode
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoWitnessStepComponents
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

theorem openedTwoTemplate (φ : Semiproposition M6.PA.RelationalSource.language 2) (hφ : φ.freeVariables = ∅)
    (a b p : M) :
    ((⌜((φ ⇜ ![#2,#0]) : Semiproposition M6.PA.RelationalSource.language 4)⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free =
      (⌜φ⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0] := by
  have ht : (⌜((φ ⇜ ![#2,#0]) : Semiproposition M6.PA.RelationalSource.language 4)⌝ : Semiformula M SourceL 4) =
      (⌜φ⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 2,Semiterm.bvar 0] := by
    rw [Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  have hf : (⌜φ⌝ : Semiformula M SourceL 2).shift = ⌜φ⌝ := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed φ hφ
  rw [ht]
  simp [Bootstrapping.Semiformula.free,Semiformula.shift_substs,hf,Semiformula.substs_substs]

theorem openedWitness_domain (a b p : M) :
    ((⌜witnessDomain4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free =
      (⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0] := by
  have hs : witnessDomain4 = domainOne ⇜ ![#2,#0] := by
    simp only [witnessDomain4,domainOne]
    ordinalSyntax
  rw [hs]
  exact openedTwoTemplate domainOne (by decide) a b p

theorem openedWitness_successor (a b p : M) :
    ((⌜witnessSuccessor4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free =
      (⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0] := by
  have hs : witnessSuccessor4 = successorTemplate ⇜ ![#2,#0] := by
    simp only [witnessSuccessor4,successorTemplate]
    ordinalSyntax
  rw [hs]
  exact openedTwoTemplate successorTemplate (by decide) a b p

noncomputable def isoWitnessStepCode (c a b p ctx dq hstep htarget : M) : M :=
  let vec := (?[ ^#(0 : M), ^&a, ^&b, ^&p] : M)
  let witness := free SourceL (subst SourceL vec (⌜matchWitnessBody4⌝ : M))
  let dom := free SourceL (subst SourceL vec (⌜witnessDomain4⌝ : M))
  let succ := free SourceL (subst SourceL vec (⌜witnessSuccessor4⌝ : M))
  let iso := free SourceL (subst SourceL vec (⌜witnessIso4⌝ : M))
  let branch := insert (neg SourceL witness) (setShift SourceL ctx)
  let dw := axL (insert witness branch) witness
  let hd := contextAndLeftCode dom (succ ^⋏ iso) branch dw
  let rest := contextAndRightCode dom (succ ^⋏ iso) branch dw
  let hs := contextAndLeftCode succ iso branch rest
  let hp := isoWitnessBranchCode c a b p ctx dq
  ordinalStepAtCode (shift SourceL c) 0 (b+1) branch hstep hd htarget hs hp

noncomputable def isoWitnessStepGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out c a b p ctx dq hstep htarget.
    ∃ wt, !(fixedFormulaQuoteGraph matchWitnessBody4) wt ∧ ∃ dt, !(fixedFormulaQuoteGraph witnessDomain4) dt ∧
    ∃ st, !(fixedFormulaQuoteGraph witnessSuccessor4) st ∧ ∃ it, !(fixedFormulaQuoteGraph witnessIso4) it ∧
    ∃ zero, !qqBvarDef zero 0 ∧ ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ v3, !adjoinDef v3 va v2 ∧ ∃ vec, !adjoinDef vec zero v3 ∧
    ∃ wb, !(substsGraph SourceL) wb vec wt ∧ ∃ db, !(substsGraph SourceL) db vec dt ∧
    ∃ sb, !(substsGraph SourceL) sb vec st ∧ ∃ ib, !(substsGraph SourceL) ib vec it ∧
    ∃ witness, !(freeGraph SourceL) witness wb ∧ ∃ dom, !(freeGraph SourceL) dom db ∧
    ∃ succ, !(freeGraph SourceL) succ sb ∧ ∃ iso, !(freeGraph SourceL) iso ib ∧
    ∃ nw, !(negGraph SourceL) nw witness ∧ ∃ shiftedCtx, !(setShiftGraph SourceL) shiftedCtx ctx ∧ ∃ branch, !insertDef branch nw shiftedCtx ∧
    ∃ wbranch, !insertDef wbranch witness branch ∧ ∃ dw, !axLGraph dw wbranch witness ∧
    ∃ si, !qqAndDef si succ iso ∧ ∃ hd, !contextAndLeftGraph hd dom si branch dw ∧
    ∃ rest, !contextAndRightGraph rest dom si branch dw ∧ ∃ hs, !contextAndLeftGraph hs succ iso branch rest ∧
    ∃ hp, !isoWitnessBranchGraph hp c a b p ctx dq ∧ ∃ cp, !(shiftGraph SourceL) cp c ∧ ∃ next, next = b + 1 ∧
    !ordinalStepAtGraph out cp 0 next branch hstep hd htarget hs hp”

theorem isoWitnessStepGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 8 → M => isoWitnessStepCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) isoWitnessStepGraph := by
  haveI := contextAndRightGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := isoWitnessBranchGraph_defined (M := M)
  haveI := ordinalStepAtGraph_defined (M := M)
  exact .mk fun w => by simp [isoWitnessStepGraph,isoWitnessStepCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoWitnessStepProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL c),stepCode_scoped _ hc.shift⟩ : Formula M SourceL)
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift))
    (htarget : T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0])
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert ((⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (b+1)])
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift) := by
  let witness : Formula M SourceL := ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let dom : Formula M SourceL := ((⌜witnessDomain4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let succ : Formula M SourceL := ((⌜witnessSuccessor4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let iso : Formula M SourceL := ((⌜witnessIso4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let branch : Sequent M SourceL := insert (∼witness) Γ.shift
  let dw : T ⊢!ᵈᵉʳ insert witness branch := TDerivation.em witness (by simp [branch]) (by simp [branch])
  let dw' := TDerivation.cast (congrArg (fun z => insert z branch) (isoMatchWitness_components a b p)) dw
  let hd := contextAndLeftProof T branch dom (succ ⋏ iso) dw'
  let rest := contextAndRightProof T branch dom (succ ⋏ iso) dw'
  let hs := contextAndLeftProof T branch succ iso rest
  let hd' := TDerivation.cast (congrArg (fun z => insert z branch) (openedWitness_domain a b p)) hd
  let hs' := TDerivation.cast (congrArg (fun z => insert z branch) (openedWitness_successor a b p)) hs
  let hp := isoWitnessBranchProof T Γ c a b p hc dq
  exact ordinalStepAtProof T branch (shift SourceL c) 0 (b+1) hc.shift hstep hd' htarget hs' hp

@[simp] theorem isoWitnessStepProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL c),stepCode_scoped _ hc.shift⟩ : Formula M SourceL)
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift))
    (htarget : T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0])
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) :
    (isoWitnessStepProof T Γ c a b p hc dq hstep htarget).val = isoWitnessStepCode c a b p Γ.val dq.val hstep.val htarget.val := by
  simp [isoWitnessStepProof,isoWitnessStepCode,Semiformula.quote_def,SemitermVec.val_succ,Sequent.shift]

#print axioms isoWitnessStepGraph_defined
#print axioms isoWitnessStepProof
#print axioms isoWitnessStepProof_val
#print axioms openedTwoTemplate
#print axioms openedWitness_domain
#print axioms openedWitness_successor
end models
end PA194IsoWitnessStepComponents
