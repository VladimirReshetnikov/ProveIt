import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194IsoWitnessComponents
import PA194IsoWitnessBranch
import PA194OrdinalStepApplicationCode
import PA194IsoWitnessStepComponents
import PA194IsoGuardMatch
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoSuccessorProperty
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

noncomputable def isoSuccessorPropertyCode (c a b p ctx du ds dg dq hstep htarget : M) : M :=
  let de := isoGuardMatchCode a b p ctx du ds dg
  let db := isoWitnessStepCode c a b p ctx dq hstep htarget
  let q := substs1 SourceL (^&b) c
  isoMatchWitnessCode a b p q ctx de db

noncomputable def isoSuccessorPropertyGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “out c a b p ctx du ds dg dq hstep htarget.
    ∃ de, !isoGuardMatchGraph de a b p ctx du ds dg ∧
    ∃ db, !isoWitnessStepGraph db c a b p ctx dq hstep htarget ∧
    ∃ tb, !qqFvarDef tb b ∧ ∃ q, !(substs1Graph SourceL) q tb c ∧
    !isoMatchWitnessGraph out a b p q ctx de db”

theorem isoSuccessorPropertyGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 11 → M => isoSuccessorPropertyCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) (w 10)) isoSuccessorPropertyGraph := by
  haveI := isoGuardMatchGraph_defined (M := M)
  haveI := isoWitnessStepGraph_defined (M := M)
  haveI := isoMatchWitnessGraph_defined (M := M)
  exact .mk fun w => by simp [isoSuccessorPropertyGraph,isoSuccessorPropertyCode]

noncomputable def isoSuccessorPropertyProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL c),stepCode_scoped _ hc.shift⟩ : Formula M SourceL)
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift))
    (htarget : T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0])
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert ((⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let q : Formula M SourceL := (⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]
  have hcshift : (⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).shift =
      (⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1) := by
    apply Semiformula.ext
    rfl
  have hq : q.shift = ((⟨shift SourceL c,by simpa using hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (b+1)]) := by
    simp [q,Semiformula.shift_substs,hcshift]
  let de := isoGuardMatchProof T Γ a b p du ds dg
  let branch := isoWitnessStepProof T Γ c a b p hc dq hstep htarget
  let db := TDerivation.cast (congrArg (fun z => insert z (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) hq.symm) branch
  exact isoMatchWitnessProof T Γ a b p q de db

@[simp] theorem isoSuccessorPropertyProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a b p : M)
    (hc : IsSemiformula SourceL 1 c)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar p]) Γ)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode (shift SourceL c),stepCode_scoped _ hc.shift⟩ : Formula M SourceL)
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift))
    (htarget : T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar (b+1),Semiterm.fvar 0])
      (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) :
    (isoSuccessorPropertyProof T Γ c a b p hc du ds dg dq hstep htarget).val =
      isoSuccessorPropertyCode c a b p Γ.val du.val ds.val dg.val dq.val hstep.val htarget.val := by
  simp [isoSuccessorPropertyProof,isoSuccessorPropertyCode,substs1,SemitermVec.val_succ]

#print axioms isoSuccessorPropertyGraph_defined
#print axioms isoSuccessorPropertyProof
#print axioms isoSuccessorPropertyProof_val
end models
end PA194IsoSuccessorProperty
