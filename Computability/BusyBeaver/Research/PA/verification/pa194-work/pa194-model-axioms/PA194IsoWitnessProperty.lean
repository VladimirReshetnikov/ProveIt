import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoMatchAtCode
import PA194IsoMatchWitness
import PA194IsoWitnessComponents
import PA194IsoGuardAt
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoWitnessProperty
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

open PA194IsoWitnessComponents PA194IsoGuardAt

noncomputable def isoWitnessPropertyCode (c a b p ctx dq dw : M) : M :=
  let dg := isoWitnessGuardCode a b p ctx dw
  isoGuardAtCode c (p+1) 0 ctx dq dg

noncomputable def isoWitnessPropertyGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out c a b p ctx dq dw. ∃ dg, !isoWitnessGuardGraph dg a b p ctx dw ∧
    ∃ next, next = p + 1 ∧ !isoGuardAtGraph out c next 0 ctx dq dg”

theorem isoWitnessPropertyGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 7 → M => isoWitnessPropertyCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) isoWitnessPropertyGraph := by
  haveI := isoWitnessGuardGraph_defined (M := M)
  haveI := isoGuardAtGraph_defined (M := M)
  exact .mk fun w => by simp [isoWitnessPropertyGraph,isoWitnessPropertyCode]

noncomputable def isoWitnessPropertyProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (c a b p : M) (hc : IsSemiformula SourceL 1 c)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c, by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (p+1)]) Γ)
    (dw : T ⊢!ᵈᵉʳ insert ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨c,by simpa using hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar 0]) Γ := by
  let dg := isoWitnessGuardProof T Γ a b p dw
  exact isoGuardAtProof T Γ c (p+1) 0 hc dq dg

@[simp] theorem isoWitnessPropertyProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (c a b p : M) (hc : IsSemiformula SourceL 1 c)
    (dq : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c, by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (p+1)]) Γ)
    (dw : T ⊢!ᵈᵉʳ insert ((⌜matchWitnessBody4⌝ : Semiformula M SourceL 4).subst
      ![Semiterm.bvar 0,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]).free Γ) :
    (isoWitnessPropertyProof T Γ c a b p hc dq dw).val = isoWitnessPropertyCode c a b p Γ.val dq.val dw.val := by
  simp [isoWitnessPropertyProof,isoWitnessPropertyCode]

#print axioms isoWitnessPropertyGraph_defined
#print axioms isoWitnessPropertyProof
#print axioms isoWitnessPropertyProof_val
end models
end PA194IsoWitnessProperty
