import PA194OccurrenceCoverage
import PA194OccurrenceStageCore
import PA194OccurrenceStable
import PA194OccurrenceStrong

/-! Primitive-recursive code for the stable PA194 occurrence predicate. -/
set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 4000000
namespace PA194OccurrenceCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryFixpointCollector PRAHistoryPairCode PRACharacteristicBit
  PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
open PA194OccurrenceStage PA194OccurrenceStageCore PA194OccurrenceStable PA194OccurrenceCoverage

/-- Test packed index `(n,v)` in the history at stage `pair(n,v)+1`. -/
def occurrenceCode (succ bit : Code 2) : Code 2 :=
  bin bit pairCode (.comp (stageCode succ) (.cons
    (.comp Code.succ (.cons pairCode (.nil 2))) (.nil 2)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

/-- Evaluation of the explicit code in every candidate-PRA model. -/
theorem modelOccurrenceCode (succ bit : Code 2) (n v : M) :
    Structure.func (L := language) (occurrenceCode succ bit) ![n,v] =
      Structure.func (L := language) bit ![pair n v,stage succ (pair n v + 1)] := by
  rw [occurrenceCode, modelBin, modelPairCode]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) j
  change Structure.func (L := language)
    (.comp (stageCode succ) (.cons (.comp Code.succ (.cons pairCode (.nil 2))) (.nil 2))) ![n,v] =
      stage succ (pair n v + 1)
  rw [modelComposition]
  change Structure.func (L := language) (stageCode succ)
    (fun i => Structure.func (L := language)
      (getCode (.cons (.comp Code.succ (.cons pairCode (.nil 2))) (.nil 2)) i) ![n,v]) =
      stage succ (pair n v + 1)
  have hv : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.comp Code.succ (.cons pairCode (.nil 2))) (.nil 2)) i) ![n,v]) =
      (fun _ : Fin 1 => pair n v + 1) := by
    funext j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    change Structure.func (L := language) (.comp Code.succ (.cons pairCode (.nil 2))) ![n,v] = _
    rw [modelComposition]
    have hh : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons pairCode (.nil 2)) i) ![n,v]) = (fun _ : Fin 1 => pair n v) := by
      funext j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelPairCode n v
    rw [hh, ←modelAddOne]
    rfl
  rw [hv]
  rfl


/-- Boolean code output is nonzero precisely when the stable history reports
occurrence. -/
theorem modelOccurrenceCode_spec (succ bit : Code 2)
    (hbitbit : PRA ⊢ bitSentence bit)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (n v : M) :
    Structure.func (L := language) (occurrenceCode succ bit) ![n,v] ≠ 0 ↔
      occurrence (stage succ) n v := by
  rw [modelOccurrenceCode]
  let x := pair n v
  let h := stage succ (x+1)
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit
  have hh := (oneCorrectSentence_iff bit PRAHistoryInsertCode.bitGraph).mp hm ![x,h]
  rw [PRAHistoryInsertCode.bitGraph, Semiformula.eval_lMap,
    PRAModelIOpenPairing.reduct_eq_standard] at hh
  have hbitmodel := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbitbit
  have hb := (bitSentence_iff bit).mp hbitmodel ![x,h]
  change Structure.func (L := language) bit ![x,h] = 0 ∨
    Structure.func (L := language) bit ![x,h] = 1 at hb
  change Structure.func (L := language) bit ![x,h] ≠ 0 ↔ bitDef.val.Evalb ![x,h]
  constructor
  · intro hne
    exact hh.mp (hb.resolve_left hne)
  · intro hmem heq
    have hone := hh.mpr hmem
    rw [heq] at hone
    exact zero_ne_one hone

/-- The exact primitive-recursive occurrence code satisfies PA194's one-step
coverage in all candidate-PRA models for any certified components. -/
theorem modelOccurrenceCode_coverage (good ins bit : Code 2)
    (hgoodbit : PRA ⊢ bitSentence good)
    (hgood : PRA ⊢ oneCorrectSentence good PA194OccurrenceCore.mappedCore)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbitbit : PRA ⊢ bitSentence bit)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (n v : M)
    (h : Structure.func (L := language) (occurrenceCode (fixSuccCode good ins) bit) ![n,v] ≠ 0) :
    0 < n ∧ (v = SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (n/4) ∨
      v = SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (n/4) ∨
      Structure.func (L := language) (occurrenceCode (fixSuccCode good ins) bit)
        ![SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (n/4),v] ≠ 0 ∨
      Structure.func (L := language) (occurrenceCode (fixSuccCode good ins) bit)
        ![SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (n/4),v] ≠ 0) := by
  let c := fixSuccCode good ins
  have hr (k s : M) : bitDef.val.Evalb ![k,stage c (s+1)] ↔
      k ≤ s ∧ PA194OccurrenceCore.occurrenceCore.val.Evalb ![k,stage c s] :=
    modelStageCore good ins bit hgoodbit hgood hins hbit k s
  have hs := modelStageStability c bit hbit hr
  have hr' (k : M) : bitDef.val.Evalb ![k,stage c (k+1)] ↔
      PA194OccurrenceCore.occurrenceCore.val.Evalb ![k,stage c k] := by
    simpa using hr k k
  have hc := staged_coverage (stage c) hr' hs n v
    ((modelOccurrenceCode_spec c bit hbitbit hbit n v).mp h)
  simpa only [←modelOccurrenceCode_spec c bit hbitbit hbit] using hc


/-- Exact four-tag recursion for the represented occurrence characteristic. -/
theorem modelOccurrenceCode_rec (good ins bit : Code 2)
    (hgoodbit : PRA ⊢ bitSentence good)
    (hgood : PRA ⊢ oneCorrectSentence good PA194OccurrenceCore.mappedCore)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbitbit : PRA ⊢ bitSentence bit)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (n v : M) :
    let c := occurrenceCode (fixSuccCode good ins) bit
    let a := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (n/4)
    let b := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (n/4)
    Structure.func (L := language) c ![n,v] ≠ 0 ↔
      0 < n ∧ ((n % 4 = 0 ∧ (Structure.func (L := language) c ![a,v] ≠ 0 ∨
                              Structure.func (L := language) c ![b,v] ≠ 0)) ∨
        ((n % 4 = 1 ∨ n % 4 = 3) ∧ (v = a ∨ v = b)) ∨
        (n % 4 = 2 ∧ (v = b ∨ Structure.func (L := language) c ![a,v] ≠ 0))) := by
  let c := fixSuccCode good ins
  have hr (k s : M) : bitDef.val.Evalb ![k,stage c (s+1)] ↔
      k ≤ s ∧ PA194OccurrenceCore.occurrenceCore.val.Evalb ![k,stage c s] :=
    modelStageCore good ins bit hgoodbit hgood hins hbit k s
  have hs := modelStageStability c bit hbit hr
  have hr' (k : M) : bitDef.val.Evalb ![k,stage c (k+1)] ↔
      PA194OccurrenceCore.occurrenceCore.val.Evalb ![k,stage c k] := by
    simpa using hr k k
  dsimp only
  rw [modelOccurrenceCode_spec c bit hbitbit hbit]
  unfold occurrence
  rw [hr', PA194OccurrenceCore.occurrenceCore_eval_rec]
  simp only [PA194OccurrenceCore.coreRecMeaning, pi₁_pair, pi₂_pair]
  by_cases hn : 0 < n
  · have hd := PA194PackedDescent.packed_children_lt n v hn
    have h1 := (hs _ _ hd.1).trans (modelOccurrenceCode_spec c bit hbitbit hbit _ _).symm
    have h2 := (hs _ _ hd.2).trans (modelOccurrenceCode_spec c bit hbitbit hbit _ _).symm
    simp only [hn, true_and, h1, h2, c]
  · simp [hn]

theorem modelOccurrenceCode_selfFresh (good ins bit : Code 2)
    (hgoodbit : PRA ⊢ bitSentence good)
    (hgood : PRA ⊢ oneCorrectSentence good PA194OccurrenceCore.mappedCore)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbitbit : PRA ⊢ bitSentence bit)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (n : M) :
    Structure.func (L := language) (occurrenceCode (fixSuccCode good ins) bit) ![n,n] = 0 := by
  apply PA194OccurrenceStrong.model_occurrence_self_fresh
    (occurrenceCode (fixSuccCode good ins) bit)
  intro a b hab
  exact modelOccurrenceCode_coverage good ins bit hgoodbit hgood hins hbitbit hbit a b hab

end models

/-- Syntactic candidate-PRA sentence saying that no code occurs in itself. -/
def selfFreshSentence (occ : Code 2) : Sentence language := ∀⁰*
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func occ ![#0,#0],.func (Code.zero 0) Fin.elim0] : Semisentence language 1)

theorem PRA_proves_occurrenceCode_selfFresh (good ins bit : Code 2)
    (hgoodbit : PRA ⊢ bitSentence good)
    (hgood : PRA ⊢ oneCorrectSentence good PA194OccurrenceCore.mappedCore)
    (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbitbit : PRA ⊢ bitSentence bit)
    (hbit : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph) :
    PRA ⊢ selfFreshSentence (occurrenceCode (fixSuccCode good ins) bit) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  simp only [models_iff, selfFreshSentence, Semiformula.eval_allClosure]
  intro e
  have h := modelOccurrenceCode_selfFresh good ins bit hgoodbit hgood hins hbitbit hbit (e 0)
  change Structure.func (L := language) (occurrenceCode (fixSuccCode good ins) bit) ![e 0,e 0] =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 at h
  have hz : (Semiterm.val (L := language) e Empty.elim ∘
      (Fin.elim0 : Fin 0 → Semiterm language Empty 1)) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ ![#0,#0]) = ![e 0,e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  simpa [Semiformula.eval_rel, eqRel, Semiterm.val_func, hz, hv] using h

/-- The needed component codes exist, and the resulting occurrence code has
an actual candidate-PRA proof of self-freshness. The codes are existentially
provided by the certified compiler; they are not yet serialized as numerals. -/
theorem PRA_has_selfFreshOccurrenceCode : ∃ good ins bit : Code 2,
    (PRA ⊢ bitSentence good) ∧
    (PRA ⊢ oneCorrectSentence good PA194OccurrenceCore.mappedCore) ∧
    (PRA ⊢ PRAHistoryInsertCode.graphSentence ins) ∧
    (PRA ⊢ bitSentence bit) ∧
    (PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph) ∧
    (PRA ⊢ selfFreshSentence (occurrenceCode (fixSuccCode good ins) bit)) := by
  obtain ⟨good, _, hgoodbit, hgood⟩ := PA194OccurrenceCore.PRA_has_occurrenceCoreCode
  obtain ⟨ins, hins⟩ := PRAHistoryInsertCode.PRA_has_insertCode
  have h : Hierarchy 𝚺 0 PRAHistoryInsertCode.bitGraph :=
    ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit, _, hbitbit, hbit⟩ := PRA_proves_boundedBooleanCharacteristic PRAHistoryInsertCode.bitGraph h
  exact ⟨good, ins, bit, hgoodbit, hgood, hins, hbitbit, hbit,
    PRA_proves_occurrenceCode_selfFresh good ins bit hgoodbit hgood hins hbitbit hbit⟩

#print axioms modelOccurrenceCode
#print axioms modelOccurrenceCode_spec
#print axioms modelOccurrenceCode_coverage
#print axioms modelOccurrenceCode_selfFresh
#print axioms modelOccurrenceCode_rec
#print axioms PRA_proves_occurrenceCode_selfFresh
#print axioms PRA_has_selfFreshOccurrenceCode
end PA194OccurrenceCode
