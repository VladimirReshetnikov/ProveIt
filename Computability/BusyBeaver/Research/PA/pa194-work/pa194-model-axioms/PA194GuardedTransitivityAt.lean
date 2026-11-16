import PA194GuardedEqualityClosed
import PA194GuardedTransitivitySyntax
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
local instance eqtransZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqtransOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqtransAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqtransMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqtransLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqtransIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardReflProof PA194ClosedEnvironment PA194FormulaDispatcher PA194PAeqBind
noncomputable local instance : adjunctiveFullSepTheory.Δ₁ := adjunctiveFullSepTheoryDelta


theorem fullSource_pointwise_transitivity (x y z : M) : GDerivable adjunctiveFullSepTheory
    (insert (neg SourceL (tr (peq (^&x) (^&y))))
      (insert (neg SourceL (tr (peq (^&y) (^&z)))) ({tr (peq (^&x) (^&z))} : M))) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have hq0 : IsSemiformula PA194PAeq.language 1 (^∀ (^∀ (transitivityMatrix : M))) := by
    have ht : IsSemiformula PA194PAeq.language 2 (^∀ (transitivityMatrix : M)) :=
      IsSemiformula.all.mpr (by simpa [show (2 : M) + 1 = 3 by norm_num] using (transitivityMatrix_valid (V := M)))
    apply IsSemiformula.all.mpr
    simpa only [one_add_one_eq_two] using ht
  have h0 : GDerivable T.theory ({tr (^∀ (^∀ (^∀ (transitivityMatrix : M))))} : M) := by
    simpa only [← transitivity_quote] using (fullSource_transitivity_guarded (M := M))
  have h1 := guarded_tr_all_specialize_guarded T hq0 h0 x
  rw [transitivity_open_first] at h1
  have hq1 : IsSemiformula PA194PAeq.language 1 (^∀ (transitivityTwo x)) :=
    IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using (transitivityTwo_valid x))
  have h2 := guarded_tr_all_specialize_guarded T hq1 h1 y
  rw [transitivity_open_second] at h2
  have h3 := guarded_tr_all_specialize_guarded T (transitivityOne_valid x y) h2 z
  rw [transitivity_open_third] at h3
  have ha : IsSemiformula PA194PAeq.language 0 (peq (^&x) (^&y)) := peq_valid (by simp) (by simp)
  have hb : IsSemiformula PA194PAeq.language 0 (peq (^&y) (^&z)) := peq_valid (by simp) (by simp)
  have hc : IsSemiformula PA194PAeq.language 0 (peq (^&x) (^&z)) := peq_valid (by simp) (by simp)
  rw [tr_or (IsSemiformula.neg_iff.mpr ha) (IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hb,hc⟩),
    tr_or (IsSemiformula.neg_iff.mpr hb) hc,tr_neg ha,tr_neg hb] at h3
  let A : M := neg SourceL (tr (peq (^&x) (^&y)))
  let B : M := neg SourceL (tr (peq (^&y) (^&z)))
  let C : M := tr (peq (^&x) (^&z))
  have hA : IsFormula SourceL A := IsSemiformula.neg_iff.mpr (tr_valid ha)
  have hB : IsFormula SourceL B := IsSemiformula.neg_iff.mpr (tr_valid hb)
  have hC : IsFormula SourceL C := tr_valid hc
  have hbc : IsFormula SourceL (B ^⋎ C) := IsSemiformula.or.mpr ⟨hB,hC⟩
  have h4 : GDerivable T.theory (insert A ({B ^⋎ C} : M)) := guarded_or_unpack hA hbc h3
  have hAset : IsFormulaSet SourceL ({A} : M) := by rw [singleton_eq_insert]; exact fs_cons hA fs_nil
  have h5 : GDerivable T.theory (insert (B ^⋎ C) ({A} : M)) := by
    apply GDerivable.wk (fs_cons hbc hAset) _ h4
    set_tac
  have h6 := guarded_or_unpack_context hB hC hAset h5
  apply GDerivable.wk (fs_cons hA (fs_cons hB (by rw [singleton_eq_insert]; exact fs_cons hC fs_nil))) _ h6
  set_tac

#print axioms fullSource_pointwise_transitivity
end models
end PA194GuardedCompiler
