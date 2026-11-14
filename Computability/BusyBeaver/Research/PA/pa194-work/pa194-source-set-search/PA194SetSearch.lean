import PA194SourceShiftHistory
import DiophantineConsistency.PRABoundedSearchUniversal
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
import DiophantineConsistency.PRAHistoryInsertCode
import DiophantineConsistency.PRABoundedFormula
/-! Internal Foundation finite-set search for a shifted source formula.

This is one all-model universal-rule search component, not a compiler or a
machine-calibration theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194SetSearch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRASubReconstruct PRAEqualityCode PRAIsZero
 PRANonzeroCharacter PRABooleanOps PRAOpenFormulaCompiler PRABoundedCharacteristic PRABoundedFormula
 PRACharacteristicBit PRAHistoryInsertCode PRABoundedSearchCode PRABoundedSearchInvariant
 PRABoundedSearchUniversal PRABoundedSearchBound
 PA194PathIterator PA194StackCode PA194StackHistory PA194TermShiftCodeModel PA194SourceShiftHistory PA194TermRecursion

theorem exists_bit : ∃ bit : Code 2, PRA ⊢ bitSentence bit ∧ PRA ⊢ oneCorrectSentence bit bitGraph := by
  have h : Hierarchy 𝚺 0 bitGraph := ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit, _, hb, hc⟩ := PRA_proves_boundedBooleanCharacteristic bitGraph h
  exact ⟨bit,hb,hc⟩
noncomputable def fixedBit : Code 2 := Classical.choose exists_bit
theorem fixedBit_bit : PRA ⊢ bitSentence fixedBit := (Classical.choose_spec exists_bit).1
theorem fixedBit_correct : PRA ⊢ oneCorrectSentence fixedBit bitGraph := (Classical.choose_spec exists_bit).2

noncomputable def memberTest : Code 3 := bin fixedBit (.proj 0) (.proj 1)
noncomputable def shiftTest : Code 3 :=
  bin equalityCode (unary fixedFormulaShiftCode (.proj 0)) (.proj 2)
noncomputable def badTest : Code 3 := notCode (andCode memberTest shiftTest)
noncomputable def setSearch : Code 3 := searchCode badTest

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bit_model (i a : M) : F fixedBit ![i,a] = 1 ↔ i ∈ a := by
  have hc := models_of_provable (inferInstance : M↓[language] ⊧* PRA) fixedBit_correct
  have h := (oneCorrectSentence_iff fixedBit bitGraph).mp hc ![i,a]
  rw [bitGraph, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
  change F fixedBit ![i,a] = 1 ↔ bitDef.val.Eval ![i,a] Empty.elim at h
  exact h.trans ((bit_defined (V := M)).iff)

theorem not_bit_zero {n : Nat} (c : Code n) (e : Fin n → M) (hbit : IsBit (F c e)) :
    F (notCode c) e = 0 ↔ F c e = 1 := by
  rw [modelNotCode]
  rcases hbit with hz | ho
  · rw [hz]
    change F isZeroCode (fun _ => (0 : M)) = 0 ↔ (0 : M) = 1
    have h : F isZeroCode (fun _ => (0 : M)) = 1 := modelIsZeroZero
    rw [h]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · rw [ho]
    change F isZeroCode (fun _ => (1 : M)) = 0 ↔ (1 : M) = 1
    have h : F isZeroCode (fun _ => (1 : M)) = 0 := by
      change F isZeroCode (fun _ => F oneCode Fin.elim0) = F (Code.zero 0) Fin.elim0
      rw [modelOneSuccZero,modelIsZeroSucc]
    rw [h]
    exact ⟨fun _ => rfl, fun _ => rfl⟩


theorem badTest_model (i a target : M)
    (hvalid : i ∈ a → IsUFormula M6.PA.RelationalSource.language i) :
    F badTest ![i,a,target] = 0 ↔
      i ∈ a ∧ shift M6.PA.RelationalSource.language i = target := by
  have hm : F memberTest ![i,a,target] = F fixedBit ![i,a] := by
    rw [memberTest,modelBin,modelProjection,modelProjection]
    rfl
  have ht : F shiftTest ![i,a,target] = F equalityCode ![F fixedFormulaShiftCode ![i], target] := by
    rw [shiftTest,modelBin,modelUnary,modelProjection,modelProjection]
    congr 2
    congr 1
    funext k
    exact Fin.cases rfl (fun j => Fin.elim0 j) k
  have hb := (bitSentence_iff fixedBit).mp
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) fixedBit_bit) ![i,a]
  have he := modelEqualityCode (F fixedFormulaShiftCode ![i]) target
  have ha := modelMulBit _ _ hb he.1
  have hab : IsBit (F (andCode memberTest shiftTest) ![i,a,target]) := by
    rw [modelAndCode,hm,ht]
    exact ha.1
  have hmul : F mulCode ![F fixedBit ![i,a], F equalityCode ![F fixedFormulaShiftCode ![i],target]] = 1 ↔
      F fixedBit ![i,a] = 1 ∧ F equalityCode ![F fixedFormulaShiftCode ![i],target] = 1 := ha.2
  rw [badTest, not_bit_zero _ _ hab, modelAndCode,hm,ht,hmul,bit_model]
  constructor
  · rintro ⟨hmem,heq⟩
    refine ⟨hmem, ?_⟩
    have heq' := he.2.mp heq
    rw [fixedFormulaShiftCode_correct (hvalid hmem)] at heq'
    exact heq'
  · rintro ⟨hmem,heq⟩
    refine ⟨hmem, he.2.mpr ?_⟩
    rw [fixedFormulaShiftCode_correct (hvalid hmem)]
    exact heq

theorem find_set (a target j : M)
    (hj : j ∈ a)
    (hvalid : ∀ i, i ∈ a → IsUFormula M6.PA.RelationalSource.language i)
    (hmatch : shift M6.PA.RelationalSource.language j = target) :
    let found := F setSearch ![a,a,target]
    found ∈ a ∧ shift M6.PA.RelationalSource.language found = target := by
  let params : ℕ → M := fun n => if n = 0 then a else target
  have hp : (fun i : Fin 2 => params i.val) = ![a,target] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [params]
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp [params]
  have hw : F badTest ![j,a,target] = 0 := (badTest_model j a target (hvalid j)).mpr ⟨hj,hmatch⟩
  have hu := modelSearchUniversal badTest a params
  have hi := modelSearchCandidateInvariant badTest a params
  rw [hp] at hu hi
  change (F setSearch ![a,a,target] = a ↔ ∀ x, x < a → F badTest ![x,a,target] ≠ 0) at hu
  change F badTest ![F setSearch ![a,a,target],a,target] = 0 ∨ F setSearch ![a,a,target] = a at hi
  have hne : F setSearch ![a,a,target] ≠ a := by
    intro he
    exact (hu.mp he j (lt_of_mem hj)) hw
  have hz : F badTest ![F setSearch ![a,a,target],a,target] = 0 := hi.resolve_right hne
  exact (badTest_model _ a target (hvalid _)).mp hz

/-- The input is exactly Foundation's internal formula-set validity and shift
membership, including arbitrary nonstandard sequents. -/
theorem find_setShift (a target : M)
    (hset : IsFormulaSet M6.PA.RelationalSource.language a)
    (htarget : target ∈ setShift M6.PA.RelationalSource.language a) :
    let found := F setSearch ![a,a,target]
    found ∈ a ∧ shift M6.PA.RelationalSource.language found = target := by
  obtain ⟨j,hj,heq⟩ := mem_setShift_iff.mp htarget
  exact find_set a target j hj (fun i hi => (hset i hi).isUFormula) heq.symm

#print axioms find_setShift

#print axioms find_set

#print axioms badTest_model

#print axioms exists_bit
#print axioms bit_model
end models
end PA194SetSearch
