import DiophantineConsistency.PRAHistoryInsertMembership
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryFixpointCollector
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRASelectCode
  PRACharacteristicBit PRABooleanOps

/-- In the step arguments [index, accumulator, previous-stage], insert the
index exactly when `good` selects it. -/
def collectStep (good ins : Code 2) : Code 3 :=
  selectAmong (bin good (.proj 0) (.proj 2))
    (bin ins (.proj 0) (.proj 1)) (.proj 1)

def collectCode (good ins : Code 2) : Code 2 :=
  .prec (.comp (.zero 0) (.nil 1)) (collectStep good ins)

/-- Collect positions 0 through s, using the supplied characteristic. -/
def fixSuccCode (good ins : Code 2) : Code 2 :=
  .comp (collectCode good ins) (.cons
    (.comp .succ (.cons (.proj 1) (.nil 2))) (.cons (.proj 0) (.nil 2)))

def invariantFormula (good ins bit : Code 2) : Semiproposition language 1 :=
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func bit ![.fvar 0,.func (collectCode good ins) ![.bvar 0,.fvar 1]],
      .func oneCode Fin.elim0] 🡘
    (Semiformula.rel Language.ORing.Rel.lt ![.fvar 0,.bvar 0] ⋏
      Semiformula.rel Language.ORing.Rel.eq ![.func good ![.fvar 0,.fvar 1],
        .func oneCode Fin.elim0]))

theorem invariantFormula_open (good ins bit : Code 2) : (invariantFormula good ins bit).Open := by
  simp [invariantFormula, LogicalConnective.iff, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelCollectBase (good ins : Code 2) (ih : M) :
    Structure.func (L := language) (collectCode good ins)
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0,ih] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (.comp (.zero 0) (.nil 1)) (collectStep good ins) ![ih]
  change Structure.func (L := language) (collectCode good ins)
    ![Structure.func (L := language) (Code.zero 0) Fin.elim0,ih] = _ at h
  rw [h]
  have hzero := modelComposition (M := M) (Code.zero 0) (.nil 1) ![ih]
  have hz : (fun i : Fin 0 => Structure.func (L := language) (getCode (.nil 1) i) ![ih]) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at hzero
  exact hzero

theorem modelCollectStep (good ins : Code 2) (i ih : M) :
    Structure.func (L := language) (collectCode good ins)
      ![Structure.func (L := language) Code.succ (fun _ => i),ih] =
      Structure.func (L := language) selectCode
        ![Structure.func (L := language) good ![i,ih],
          Structure.func (L := language) ins ![i,Structure.func (L := language) (collectCode good ins) ![i,ih]],
          Structure.func (L := language) (collectCode good ins) ![i,ih]] := by
  have h := modelStep (M := M) (.comp (.zero 0) (.nil 1)) (collectStep good ins) ![i,ih]
  change Structure.func (L := language) (collectCode good ins)
      ![Structure.func (L := language) Code.succ (fun _ => i),ih] =
    Structure.func (L := language) (collectStep good ins)
      ![i,Structure.func (L := language) (collectCode good ins) ![i,ih],ih] at h
  rw [h,collectStep,modelSelectAmong,modelBin,modelBin]
  simp only [modelProjection]
  rfl
theorem modelCollectMembershipStep (good ins : Code 2)
    (hbit : PRA ⊢ bitSentence good) (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (i ih k : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
      rw [PRAModelIOpenPairing.reduct_eq_standard] at h
      exact h
    bitDef.val.Evalb ![k,Structure.func (L := language) (collectCode good ins)
      ![Structure.func (L := language) Code.succ (fun _ => i),ih]] ↔
      (k = i ∧ Structure.func (L := language) good ![i,ih] =
        Structure.func (L := language) oneCode Fin.elim0) ∨
        bitDef.val.Evalb ![k,Structure.func (L := language) (collectCode good ins) ![i,ih]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  let a := Structure.func (L := language) (collectCode good ins) ![i,ih]
  let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => k)
  let q := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
  have hp := (PRAHistoryExpCode.graph_iff k p).mp (PRAHistoryExpCode.modelExpCode k)
  have hq := (PRAHistoryExpCode.graph_iff i q).mp (PRAHistoryExpCode.modelExpCode i)
  have hb := (bitSentence_iff good).mp
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit) ![i,ih]
  rw [modelCollectStep]
  by_cases ht : Structure.func (L := language) good ![i,ih] =
      Structure.func (L := language) oneCode Fin.elim0
  · rw [ht,modelSelectOne]
    have hin := PRAHistorySeqConsCode.modelInsert ins hins i a
    rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hin
    simpa [a,ht] using PRAHistoryInsertMembership.insert_membership
      (Structure.func (L := language) ins ![i,a]) k i a p q hp hq hin
  · have hz : Structure.func (L := language) good ![i,ih] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      rcases hb with hz | ho
      · exact hz
      · exact False.elim (ht ho)
    rw [hz,modelSelectZero]
    have hn : Structure.func (L := language) (Code.zero 0) Fin.elim0 ≠
        (Structure.func (L := language) oneCode Fin.elim0 : M) :=
      Ne.symm PRANonzeroCharacter.modelOneNeZero
    simp [hn]
theorem modelCollectInvariant (good ins bit : Code 2)
    (hbit : PRA ⊢ bitSentence good) (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hcorrect : PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (n k ih : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
      rw [PRAModelIOpenPairing.reduct_eq_standard] at h
      exact h
    bitDef.val.Evalb ![k,Structure.func (L := language) (collectCode good ins) ![n,ih]] ↔
      k < n ∧ Structure.func (L := language) good ![k,ih] =
        Structure.func (L := language) oneCode Fin.elim0 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  let e : ℕ → M := fun j => if j = 0 then k else ih
  have e0 : e 0 = k := by simp [e]
  have e1 : e 1 = ih := by simp [e]
  have correct (a : M) : Structure.func (L := language) bit ![k,a] =
      Structure.func (L := language) oneCode Fin.elim0 ↔ bitDef.val.Evalb ![k,a] := by
    have hc := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect
    have h := PRABoundedWitness.modelCharacteristicMatrix bit PRAHistoryInsertCode.bitGraph hc ![k,a]
    have hz : (Semiterm.val (L := language) ![k,a] Empty.elim ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    have hv : (Semiterm.val (L := language) ![k,a] Empty.elim ∘ vars 2) = ![k,a] := by
      funext j
      refine Fin.cases rfl (fun l => ?_) j
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    have hh : PRAHistoryInsertCode.bitGraph.Eval ![k,a] Empty.elim ↔ bitDef.val.Evalb ![k,a] := by
      rw [PRAHistoryInsertCode.bitGraph, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
    simpa [PRABoundedWitness.characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode,
      Semiterm.val_func, hz, hv, hh] using h
  have heval (x : M) : (invariantFormula good ins bit).Eval ![x] e ↔
      (bitDef.val.Evalb ![k,Structure.func (L := language) (collectCode good ins) ![x,ih]] ↔
        k < x ∧ Structure.func (L := language) good ![k,ih] =
          Structure.func (L := language) oneCode Fin.elim0) := by
    have hz : (Semiterm.val (L := language) ![x] e ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    have hrel : Structure.rel (L := language) Language.ORing.Rel.lt ![k,x] ↔ k < x := Iff.rfl
    simp [invariantFormula, LogicalConnective.iff, Semiformula.eval_rel, eqRel,
      Semiterm.val_func, e0, e1, hz, correct, iff_def, hrel]
  have hzero : ¬bitDef.val.Evalb ![k,(0 : M)] := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => k)
    have hp := (PRAHistoryExpCode.graph_iff k p).mp (PRAHistoryExpCode.modelExpCode k)
    intro hb
    have hl := (PRAHistoryInsertMembership.bit_iff_lenbit k 0 p hp).mp hb
    exact not_lt_of_ge hl.le hp.range_pos
  have hbase : (invariantFormula good ins bit).Eval
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e := by
    apply (heval 0).mpr
    change bitDef.val.Evalb ![k,Structure.func (L := language) (collectCode good ins)
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0,ih]] ↔ _
    rw [modelCollectBase]
    change ¬bitDef.val.Evalb ![k,Structure.func (L := language) (Code.zero 0) Fin.elim0] at hzero
    simp [hzero]
  have hstep (x : M) (hx : (invariantFormula good ins bit).Eval ![x] e) :
      (invariantFormula good ins bit).Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e := by
    apply (heval _).mpr
    have hi := (heval x).mp hx
    rw [modelCollectMembershipStep good ins hbit hins x ih k,hi, ←modelAddOne]
    change (k = x ∧ Structure.func (L := language) good ![x,ih] = _ ∨
      k < x ∧ Structure.func (L := language) good ![k,ih] = _) ↔
      k < x+1 ∧ Structure.func (L := language) good ![k,ih] = _
    have hk : k < x+1 ↔ k = x ∨ k < x := by
      simpa [or_comm, eq_comm] using (lt_succ_iff_le (x := k) (y := x)).trans le_iff_lt_or_eq
    rw [hk]
    by_cases h : k = x
    · simp [h]
    · simp [h]
  have result := PRAOpenInduction.modelOpenInduction (invariantFormula good ins bit)
    (invariantFormula_open good ins bit) e hbase hstep n
  exact (heval n).mp result
end models
end DiophantineConsistency.PRAHistoryFixpointCollector
