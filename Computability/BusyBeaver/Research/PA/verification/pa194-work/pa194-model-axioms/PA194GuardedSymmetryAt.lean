import PA194GuardedEqualityClosed
import PA194GuardedSymmetrySyntax
import PA194GuardedUniversalElim
import PA194GuardedDisjunctionElim
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open PA194ContextSpecializeCode PA194ContextModusPonensCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance eqsymZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqsymOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqsymAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqsymMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqsymLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqsymIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardReflProof PA194ClosedEnvironment PA194FormulaDispatcher PA194PAeqBind
noncomputable local instance : adjunctiveFullSepTheory.Δ₁ := adjunctiveFullSepTheoryDelta


theorem fullSource_pointwise_symmetry (y z : M) : GDerivable adjunctiveFullSepTheory
    (insert (neg SourceL (tr (peq (^&y) (^&z)))) ({tr (peq (^&z) (^&y))} : M)) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have hq : IsSemiformula PA194PAeq.language 1 (^∀ (symmetryMatrix : M)) :=
    IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using (symmetryMatrix_valid (V := M)))
  have h0 : GDerivable T.theory ({tr (^∀ (^∀ (symmetryMatrix : M)))} : M) := by
    simpa only [← symmetry_quote] using (fullSource_symmetry_guarded (M := M))
  have h1 := guarded_tr_all_specialize_guarded T hq h0 y
  rw [symmetry_open_first] at h1
  have h2 := guarded_tr_all_specialize_guarded T (symmetryOne_valid y) h1 z
  rw [symmetry_open_second] at h2
  have ha : IsSemiformula PA194PAeq.language 0 (peq (^&y) (^&z)) := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 0 (peq (^&z) (^&y)) := peq_valid (by simp) (by simp)
  rw [tr_or (IsSemiformula.neg_iff.mpr ha) hb, tr_neg ha] at h2
  exact guarded_or_unpack (IsSemiformula.neg_iff.mpr (tr_valid ha)) (tr_valid hb) h2

#print axioms fullSource_pointwise_symmetry
end models
end PA194GuardedCompiler
