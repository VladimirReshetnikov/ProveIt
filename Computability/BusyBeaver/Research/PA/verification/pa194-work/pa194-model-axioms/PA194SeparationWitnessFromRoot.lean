import PA194SeparationTraceWitness
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SeparationWitnessFromRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Specialize separation, then eliminate its existential trace witness. -/
noncomputable def separationWitnessCode (p s q g ds db : M) : M :=
  let de := traceFromSepCode p s g ds
  traceWitnessElimCode p s q g de db

noncomputable def separationWitnessGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p s q g ds db. ∃ de, !traceFromSepGraph de p s g ds ∧
    !traceWitnessElimGraph out p s q g de db”

theorem separationWitnessGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => separationWitnessCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) separationWitnessGraph := by
  haveI := traceFromSepGraph_defined (M := M)
  haveI := traceWitnessElimGraph_defined (M := M)
  exact .mk fun v => by simp [separationWitnessGraph,separationWitnessCode]

noncomputable def separationWitnessProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p) (q : Formula M SourceL)
    (ds : T ⊢!ᵈᵉʳ insert (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼(⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let de := traceFromSepProof T Γ p s hp ds
  exact traceWitnessElimProof T Γ p s hp q de db

@[simp] theorem separationWitnessProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s : M) (hp : IsSemiformula SourceL 1 p) (q : Formula M SourceL)
    (ds : T ⊢!ᵈᵉʳ insert (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼(⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ.shift)) :
    (separationWitnessProof T Γ p s hp q ds db).val = separationWitnessCode p s q.val Γ.val ds.val db.val := by
  simp [separationWitnessProof,separationWitnessCode]

#print axioms separationWitnessGraph_defined
#print axioms separationWitnessProof
#print axioms separationWitnessProof_val
end models
end PA194SeparationWitnessFromRoot
