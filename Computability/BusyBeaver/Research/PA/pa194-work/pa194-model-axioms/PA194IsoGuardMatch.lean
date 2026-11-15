import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoGuardMatch
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

theorem isoGuard_match_components (a b p : M) :
    ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      ((⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) ⋏
      ((⌜matchIsoBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) := by
  have hs : matchDomainBound3 ⋏ matchIsoBound3 = isoGuardTemplate ⇜ ![#1,#0] := by
    simp only [isoGuardTemplate,matchDomainBound3,matchIsoBound3]
    isoSyntax
  have ht : (⌜(matchDomainBound3 ⋏ matchIsoBound3)⌝ : Semiformula M SourceL 3) =
      (⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 1,Semiterm.bvar 0] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  have hi := congrArg (fun f : Semiformula M SourceL 3 => (f.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : Formula M SourceL)) ht
  simpa [Semiformula.substs_substs] using hi.symm

noncomputable def isoGuardMatchCode (a b p ctx du ds dg : M) : M :=
  let vec := (?[ ^&a, ^&b, ^&p] : M)
  let dom := subst SourceL vec (⌜matchDomainBound3⌝ : M)
  let iso := subst SourceL vec (⌜matchIsoBound3⌝ : M)
  let hd := contextAndLeftCode dom iso ctx dg
  let hi := contextAndRightCode dom iso ctx dg
  isoMatchAtCode a b p ctx du hd ds hi

noncomputable def isoGuardMatchGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out a b p ctx du ds dg. ∃ d0, !(fixedFormulaQuoteGraph matchDomainBound3) d0 ∧
    ∃ i0, !(fixedFormulaQuoteGraph matchIsoBound3) i0 ∧
    ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ vec, !adjoinDef vec va v2 ∧
    ∃ dom, !(substsGraph SourceL) dom vec d0 ∧ ∃ iso, !(substsGraph SourceL) iso vec i0 ∧
    ∃ hd, !contextAndLeftGraph hd dom iso ctx dg ∧ ∃ hi, !contextAndRightGraph hi dom iso ctx dg ∧
    !isoMatchAtGraph out a b p ctx du hd ds hi”

theorem isoGuardMatchGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 7 → M => isoGuardMatchCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) isoGuardMatchGraph := by
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := contextAndRightGraph_defined (M := M)
  haveI := isoMatchAtGraph_defined (M := M)
  exact .mk fun w => by simp [isoGuardMatchGraph,isoGuardMatchCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoGuardMatchProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜matchGoalBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ := by
  let dom : Formula M SourceL := (⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]
  let iso : Formula M SourceL := (⌜matchIsoBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]
  let d := TDerivation.cast (congrArg (fun z => insert z Γ) (isoGuard_match_components a b p)) dg
  let hd := contextAndLeftProof T Γ dom iso d
  let hi := contextAndRightProof T Γ dom iso d
  exact isoMatchAtProof T Γ a b p du hd ds hi

@[simp] theorem isoGuardMatchProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    (isoGuardMatchProof T Γ a b p du ds dg).val = isoGuardMatchCode a b p Γ.val du.val ds.val dg.val := by
  simp [isoGuardMatchProof,isoGuardMatchCode,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoGuardMatchGraph_defined
#print axioms isoGuardMatchProof
#print axioms isoGuardMatchProof_val
#print axioms isoGuard_match_components
end models
end PA194IsoGuardMatch
