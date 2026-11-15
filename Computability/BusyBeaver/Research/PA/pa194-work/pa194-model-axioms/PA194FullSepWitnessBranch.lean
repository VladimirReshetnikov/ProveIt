import PA194SeparationWitnessFromRoot
import PA194FullSepOpen
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 250000
namespace PA194FullSepWitnessBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194FullSepOpen PA194SeparationWitnessFromRoot PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- The explicit classifier-defined adjunctive source theory. -/
noncomputable def fullSourceInternal : InternalTheory M SourceL :=
  ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩

/-- The source itself supplies separation; only the witness branch remains. -/
noncomputable def fullSepWitnessBranchProof (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p) (q : Formula M SourceL)
    (db : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q.shift (insert (∼(⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ.shift)) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert q Γ := by
  let sep : Formula M SourceL := ⟨sepRoot p, sepRoot_scoped p hp⟩
  have hsep : (fullSourceInternal (M := M)) ⊢ sep := by
    apply (TProvable.iff_provable).2
    exact adjunctive_full_sep_root_provable p hp
  let ds : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert sep Γ :=
    TDerivation.wk hsep.get (by intro x hx; simp at hx ⊢; tauto)
  exact separationWitnessProof (fullSourceInternal (M := M)) Γ p s hp q ds db

#print axioms fullSourceInternal
#print axioms fullSepWitnessBranchProof
end models
end PA194FullSepWitnessBranch
