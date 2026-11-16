import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoWitnessComponents
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

def witnessDomain4 : Semiproposition M6.PA.RelationalSource.language 4 := Ordinal.domain (.bvar 0)
def witnessSuccessor4 : Semiproposition M6.PA.RelationalSource.language 4 := Ordinal.successor (.bvar 0) (.bvar 2)
def witnessIso4 : Semiproposition M6.PA.RelationalSource.language 4 := orderIso (.bvar 3) (.bvar 0)

theorem isoMatchWitness_components (a b p : M) :
    ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free =
    ((⌜witnessDomain4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free ⋏
      (((⌜witnessSuccessor4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free ⋏
      ((⌜witnessIso4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) := by
  have hb : (⌜matchWitnessBody4⌝ : Semiformula M SourceL 4) =
      (⌜witnessDomain4⌝ : Semiformula M SourceL 4) ⋏
      ((⌜witnessSuccessor4⌝ : Semiformula M SourceL 4) ⋏ (⌜witnessIso4⌝ : Semiformula M SourceL 4)) := by
    simp [matchWitnessBody4,witnessDomain4,witnessSuccessor4,witnessIso4]
  rw [hb]
  simp [Bootstrapping.Semiformula.free]

theorem isoMatchWitness_guard (a b p : M) :
    ((⌜witnessDomain4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free ⋏
      ((⌜witnessIso4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free =
    (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (p+1)] := by
  have hs : witnessDomain4 ⋏ witnessIso4 = isoGuardTemplate ⇜ ![#0,#3] := by
    simp only [witnessDomain4,witnessIso4,isoGuardTemplate]
    isoSyntax
  have ht : (⌜(witnessDomain4 ⋏ witnessIso4)⌝ : Semiformula M SourceL 4) =
      (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.bvar 3] := by
    rw [hs,Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  have hf : (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).shift = ⌜isoGuardTemplate⌝ := by
    apply Semiformula.ext
    exact PA194InternalInductionBaseShift.typed_quote_shift_fixed isoGuardTemplate (by decide)
  have hi := congrArg (fun f : Semiformula M SourceL 4 =>
    (f.subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) ht
  simpa [Bootstrapping.Semiformula.free,Semiformula.shift_substs,hf,Semiformula.substs_substs] using hi

noncomputable def isoWitnessGuardCode (a b p ctx dw : M) : M :=
  let vec := (?[ ^#(0 : M), ^&a, ^&b, ^&p] : M)
  let dom := free SourceL (subst SourceL vec (⌜witnessDomain4⌝ : M))
  let succ := free SourceL (subst SourceL vec (⌜witnessSuccessor4⌝ : M))
  let iso := free SourceL (subst SourceL vec (⌜witnessIso4⌝ : M))
  let rest := contextAndRightCode dom (succ ^⋏ iso) ctx dw
  let diso := contextAndRightCode succ iso ctx rest
  let ddom := contextAndLeftCode dom (succ ^⋏ iso) ctx dw
  contextAndCode dom iso ctx ddom diso

noncomputable def isoWitnessGuardGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out a b p ctx dw. ∃ d0, !(fixedFormulaQuoteGraph witnessDomain4) d0 ∧
    ∃ s0, !(fixedFormulaQuoteGraph witnessSuccessor4) s0 ∧ ∃ i0, !(fixedFormulaQuoteGraph witnessIso4) i0 ∧
    ∃ zero, !qqBvarDef zero 0 ∧ ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ v3, !adjoinDef v3 va v2 ∧ ∃ vec, !adjoinDef vec zero v3 ∧
    ∃ db, !(substsGraph SourceL) db vec d0 ∧ ∃ sb, !(substsGraph SourceL) sb vec s0 ∧ ∃ ib, !(substsGraph SourceL) ib vec i0 ∧
    ∃ dom, !(freeGraph SourceL) dom db ∧ ∃ succ, !(freeGraph SourceL) succ sb ∧ ∃ iso, !(freeGraph SourceL) iso ib ∧
    ∃ si, !qqAndDef si succ iso ∧ ∃ rest, !contextAndRightGraph rest dom si ctx dw ∧
    ∃ diso, !contextAndRightGraph diso succ iso ctx rest ∧ ∃ ddom, !contextAndLeftGraph ddom dom si ctx dw ∧
    !contextAndGraph out dom iso ctx ddom diso”

theorem isoWitnessGuardGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 5 → M => isoWitnessGuardCode (w 0) (w 1) (w 2) (w 3) (w 4)) isoWitnessGuardGraph := by
  haveI := contextAndRightGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextAndGraph_defined (M := M)
  exact .mk fun w => by simp [isoWitnessGuardGraph,isoWitnessGuardCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoWitnessGuardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (dw : T ⊢!ᵈᵉʳ insert ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (p+1)]) Γ := by
  let dom : Formula M SourceL := ((⌜witnessDomain4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let succ : Formula M SourceL := ((⌜witnessSuccessor4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let iso : Formula M SourceL := ((⌜witnessIso4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free
  let dw' := TDerivation.cast (congrArg (fun z => insert z Γ) (isoMatchWitness_components a b p)) dw
  let rest := contextAndRightProof T Γ dom (succ ⋏ iso) dw'
  let diso := contextAndRightProof T Γ succ iso rest
  let ddom := contextAndLeftProof T Γ dom (succ ⋏ iso) dw'
  let dout := contextAndProof T Γ dom iso ddom diso
  exact TDerivation.cast (congrArg (fun z => insert z Γ) (isoMatchWitness_guard a b p)) dout

@[simp] theorem isoWitnessGuardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (dw : T ⊢!ᵈᵉʳ insert ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free Γ) :
    (isoWitnessGuardProof T Γ a b p dw).val = isoWitnessGuardCode a b p Γ.val dw.val := by
  simp [isoWitnessGuardProof,isoWitnessGuardCode,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoWitnessGuardGraph_defined
#print axioms isoWitnessGuardProof
#print axioms isoWitnessGuardProof_val
#print axioms isoMatchWitness_guard
#print axioms isoMatchWitness_components
end models
end PA194IsoWitnessComponents
