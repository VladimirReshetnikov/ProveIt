import PA194OccurrenceStage
import PA194OccurrenceCore

/-! Exact one-stage recurrence for the PA194 occurrence decoder. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
namespace PA194OccurrenceStageCore
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryFixpointSuccCode PRAHistoryFixpointCollector PRACharacteristicBit
  PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
open PA194OccurrenceStage PA194OccurrenceCore

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Every update evaluates the exact four-tag occurrence core against the
previous history, at all model stages. The given codes are assumed certified
by candidate PRA. -/
theorem modelStageCore (good ins bit : Code 2)
    (hgoodbit : PRA ⊢ bitSentence good)
    (hgood : PRA ⊢ oneCorrectSentence good mappedCore)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (k s : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    bitDef.val.Evalb ![k,stage (fixSuccCode good ins) (s+1)] ↔
      k ≤ s ∧ occurrenceCore.val.Evalb ![k,stage (fixSuccCode good ins) s] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  let ih := stage (fixSuccCode good ins) s
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hgood
  have h := modelCharacteristicMatrix good mappedCore hm ![k,ih]
  have hz : (Semiterm.val (L := language) ![k,ih] Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) ![k,ih] Empty.elim ∘ vars 2) = ![k,ih] := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) l
  have hc : Structure.func (L := language) good ![k,ih] =
      Structure.func (L := language) oneCode Fin.elim0 ↔ occurrenceCore.val.Evalb ![k,ih] := by
    have hc' : Structure.func (L := language) good ![k,ih] =
        Structure.func (L := language) oneCode Fin.elim0 ↔ mappedCore.Eval ![k,ih] Empty.elim := by
      simpa [characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode,
        Semiterm.val_func, hz, hv] using h
    rw [mappedCore, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hc'
    exact hc'
  rw [modelStageMembership good ins bit hgoodbit hins hbit]
  exact and_congr_right (fun _ => hc)
/-- The stage equation expanded into PA194's exact decoded-child recursion. -/
theorem modelStageRec (good ins bit : Code 2)
    (hgoodbit : PRA ⊢ bitSentence good)
    (hgood : PRA ⊢ oneCorrectSentence good mappedCore)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (k s : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
    bitDef.val.Evalb ![k,stage (fixSuccCode good ins) (s+1)] ↔
      k ≤ s ∧ coreRecMeaning k (stage (fixSuccCode good ins) s) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  rw [modelStageCore good ins bit hgoodbit hgood hins hbit, occurrenceCore_eval_rec]
end models

/-- Candidate PRA certifies every component used in the exact stage update. -/
theorem PRA_has_stage_components : ∃ good ins bit : Code 2,
    (PRA ⊢ bitSentence good) ∧ (PRA ⊢ oneCorrectSentence good mappedCore) ∧
    (PRA ⊢ PRAHistoryInsertCode.graphSentence ins) ∧
    (PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph) := by
  obtain ⟨good, _, hgoodbit, hgood⟩ := PRA_has_occurrenceCoreCode
  obtain ⟨ins, hins⟩ := PRAHistoryInsertCode.PRA_has_insertCode
  have h : Hierarchy 𝚺 0 PRAHistoryInsertCode.bitGraph :=
    ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit, _, _, hbit⟩ := PRA_proves_boundedBooleanCharacteristic PRAHistoryInsertCode.bitGraph h
  exact ⟨good, ins, bit, hgoodbit, hgood, hins, hbit⟩

#print axioms PRA_has_stage_components
#print axioms modelStageCore
#print axioms modelStageRec
end PA194OccurrenceStageCore
