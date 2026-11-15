import PA194GreatestSuccessorAtCode
import PA194GreatestSuccessorClosedModel
import PA194FullSepWitnessBranch
import PA194DomainInstances
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194GreatestMemberProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194GreatestSuccessorAtCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def greatestTailBM2 : Semiproposition M6.PA.RelationalSource.language 2 :=
  ∀⁰ (mem (.bvar 2) (.bvar 0) 🡒 (eq (.bvar 0) (.bvar 1) ⋎ mem (.bvar 1) (.bvar 0)))

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

/-- The greatest predicate begins with membership of the proposed predecessor. -/
theorem greatestAt_decompose (b m : M) :
    ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b] : Formula M SourceL) =
      (Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b] ⋏
       ((⌜greatestTailBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b])) := by
  have he : (⌜greatestBM2⌝ : Semiformula M SourceL 2) =
      (⌜(mem (.bvar 1) (.bvar 0) : Semiproposition M6.PA.RelationalSource.language 2)⌝ : Semiformula M SourceL 2) ⋏ ⌜greatestTailBM2⌝ := by
    simp [greatestBM2,greatest,greatestTailBM2,mem,eq,sourceImply]
  rw [he]
  simp only [Semiformula.substs_and]
  congr 1
  apply Semiformula.ext
  simp [Semiformula.typedQuote, Semiformula.quote_def, mem, SemitermVec.val_succ, substs1, Matrix.vecHead, Matrix.vecTail]

noncomputable def greatestMemberCode (b m g d : M) : M :=
  let mem := memberFvarCode m b
  let rest := subst SourceL (?[ ^&m, ^&b] : M) (⌜greatestTailBM2⌝ : M)
  contextAndLeftCode mem rest g d

noncomputable def greatestMemberGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out b m g d. ∃ mem, !memberFvarGraph mem m b ∧ ∃ tail, !(fixedFormulaQuoteGraph greatestTailBM2) tail ∧
    ∃ tm, !qqFvarDef tm m ∧ ∃ tb, !qqFvarDef tb b ∧ ∃ v, !adjoinDef v tb 0 ∧ ∃ vec, !adjoinDef vec tm v ∧
    ∃ rest, !(substsGraph SourceL) rest vec tail ∧ !contextAndLeftGraph out mem rest g d”

theorem greatestMemberGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => greatestMemberCode (v 0) (v 1) (v 2) (v 3)) greatestMemberGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  exact .mk fun v => by simp [greatestMemberGraph,greatestMemberCode,fixedFormulaQuoteGraph_correct]

noncomputable def greatestMemberProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (b m : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ := by
  let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]
  let rest : Formula M SourceL := (⌜greatestTailBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]
  let d' := TDerivation.cast (congrArg (fun q => insert q Γ) (greatestAt_decompose b m)) d
  exact contextAndLeftProof T Γ mc rest d'

@[simp] theorem greatestMemberProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (b m : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    (greatestMemberProof T Γ b m d).val = greatestMemberCode b m Γ.val d.val := by
  have hm : ((Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL).val = memberFvarCode m b := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [greatestMemberProof,greatestMemberCode,contextAndLeftProof_val,TDerivation.cast_val,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hm,Semiformula.quote_def]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms greatestMemberGraph_defined
#print axioms greatestMemberProof
#print axioms greatestMemberProof_val
#print axioms greatestAt_decompose
end models
end PA194GreatestMemberProjection
