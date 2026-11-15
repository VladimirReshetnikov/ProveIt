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
namespace PA194IsoMatchWitness
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

def matchWitnessBody4 : Semiproposition M6.PA.RelationalSource.language 4 :=
  Ordinal.domain (.bvar 0) ⋏ (Ordinal.successor (.bvar 0) (.bvar 2) ⋏ orderIso (.bvar 3) (.bvar 0))

theorem isoMatchGoal_expanded (a b p : M) :
    ((⌜matchGoalBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : Formula M SourceL) =
      ∃⁰ ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) := by
  have hs : matchGoalBound3 = ∃⁰ matchWitnessBody4 := by
    simp [matchGoalBound3,isoPredecessorMatch,matchWitnessBody4]
  have ht : (⌜matchGoalBound3⌝ : Semiformula M SourceL 3) = ∃⁰ (⌜matchWitnessBody4⌝ : Semiformula M SourceL 4) := by
    rw [hs]
    simp
  rw [ht,Semiformula.substs_ex]
  congr 1
  have hv : SemitermVec.q (![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : SemitermVec M SourceL 3 0) =
      (![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : SemitermVec M SourceL 4 1) := by
    funext i
    fin_cases i <;> simp [SemitermVec.q]
  rw [hv]

noncomputable def isoMatchWitnessCode (a b p q ctx de db : M) : M :=
  let vec := (?[ ^#(0 : M), ^&a, ^&b, ^&p] : M)
  let body := subst SourceL vec (⌜matchWitnessBody4⌝ : M)
  contextExsElimCode body q ctx de db

noncomputable def isoMatchWitnessGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out a b p q ctx de db. ∃ tmpl, !(fixedFormulaQuoteGraph matchWitnessBody4) tmpl ∧
    ∃ zero, !qqBvarDef zero 0 ∧ ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ v3, !adjoinDef v3 va v2 ∧ ∃ vec, !adjoinDef vec zero v3 ∧
    ∃ body, !(substsGraph SourceL) body vec tmpl ∧ !contextExsElimGraph out body q ctx de db”

theorem isoMatchWitnessGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 7 → M => isoMatchWitnessCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) isoMatchWitnessGraph := by
  haveI := contextExsElimGraph_defined (M := M)
  exact .mk fun w => by simp [isoMatchWitnessGraph,isoMatchWitnessCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoMatchWitnessProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜matchGoalBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let body : Semiformula M SourceL 1 := (⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]
  let de' := TDerivation.cast (congrArg (fun z => insert z Γ) (isoMatchGoal_expanded a b p)) de
  exact PA194ContextExsWitnessCode.contextExsElimWitness T Γ body q de' db

@[simp] theorem isoMatchWitnessProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜matchGoalBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free) Γ.shift)) :
    (isoMatchWitnessProof T Γ a b p q de db).val = isoMatchWitnessCode a b p q.val Γ.val de.val db.val := by
  simp [isoMatchWitnessProof,isoMatchWitnessCode,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoMatchWitnessGraph_defined
#print axioms isoMatchWitnessProof
#print axioms isoMatchWitnessProof_val
#print axioms isoMatchGoal_expanded
end models
end PA194IsoMatchWitness
