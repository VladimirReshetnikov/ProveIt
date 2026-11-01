import DiophantineConsistency.PRAHistoryExpCode
import DiophantineConsistency.PRAHistoryPairCode
import Foundation.FirstOrder.Arithmetic.Exponential.Bit
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryInsertCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASelectCode
  PRABooleanOps PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula
  PRABoundedWitness PRAHistoryExpCode PRAHistoryPairCode

theorem insert_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (b i a : V) :
    insertDef.val.Evalb ![b,i,a] ↔
      (bitDef.val.Evalb ![i,a] ∧ b = a) ∨
      (¬bitDef.val.Evalb ![i,a] ∧ ∃ e ≤ b, expDef.val.Evalb ![e,i] ∧ b = a+e) := by
  simp [insertDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, Semiformula.Operator.val, operator_mem_def,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]

def bitGraph : Semisentence language 2 := Semiformula.lMap embedding bitDef.val

def insertCode (bit : Code 2) : Code 2 :=
  selectAmong bit (.proj 1)
    (bin addCode (.proj 1) (.comp expCode (.cons (.proj 0) (.nil 2))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelInsertCode (bit : Code 2) (hbit : PRA ⊢ bitSentence bit)
    (hcorrect : PRA ⊢ oneCorrectSentence bit bitGraph) (i a : M) :
    (Semiformula.lMap embedding insertDef.val).Eval
      ![Structure.func (L := language) (insertCode bit) ![i,a],i,a] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  let e := Structure.func (L := language) expCode (fun _ => i)
  have hex : expDef.val.Evalb ![e,i] := by
    have h := modelExpCode i
    rw [expGraph, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
    simpa [expDef, Semiformula.eval_substs] using h
  have hiff : bitGraph.Eval ![i,a] Empty.elim ↔ bitDef.val.Evalb ![i,a] := by
    rw [bitGraph, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have hc := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect
  have hb := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit
  have hb' := (bitSentence_iff bit).mp hb ![i,a]
  have hcm := modelCharacteristicMatrix bit bitGraph hc ![i,a]
  have hz : (Semiterm.val (L := language) ![i,a] Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) ![i,a] Empty.elim ∘ vars 2) = ![i,a] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have hchar : Structure.func (L := language) bit ![i,a] =
      Structure.func (L := language) oneCode Fin.elim0 ↔ bitDef.val.Evalb ![i,a] := by
    simpa [characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode,
      Semiterm.val_func, hz, hv, hiff] using hcm
  have hval : Structure.func (L := language) (insertCode bit) ![i,a] =
      Structure.func (L := language) selectCode
        ![Structure.func (L := language) bit ![i,a], a, a+e] := by
    rw [insertCode, modelSelectAmong, modelBin]
    simp only [modelProjection]
    congr 1
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change Structure.func (L := language) addCode ![a, _] = _
    congr 1
    rw [modelComposition]
    congr 1
    funext k
    refine Fin.cases ?_ (fun m => Fin.elim0 m) k
    have hp : (fun j : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.proj 0) (.nil 2)) j) ![i,a]) = (fun _ => i) := by
      funext j
      refine Fin.cases ?_ (fun m => Fin.elim0 m) j
      exact modelProjection 0 ![i,a]
    rw [hp]
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard, insert_iff, hval]
  by_cases h : bitDef.val.Evalb ![i,a]
  · rw [(hchar.mpr h), modelSelectOne]
    exact Or.inl ⟨h,rfl⟩
  · have hzero : Structure.func (L := language) bit ![i,a] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      rcases hb' with hz | ho
      · exact hz
      · exact False.elim (h (hchar.mp ho))
    rw [hzero, modelSelectZero]
    right
    refine ⟨h,e,?_,hex,rfl⟩
    exact le_add_left (le_refl e)
def graphRew (c : Code 2) : Rew language Empty 3 Empty 2 := Rew.embSubsts
  ![.func c ![#0,#1],#0,#1]

def graphSentence (c : Code 2) : Sentence language := ∀⁰*
  (graphRew c ▹ Semiformula.lMap embedding insertDef.val)

theorem modelGraphSentence (bit : Code 2) (hb : PRA ⊢ bitSentence bit)
    (hc : PRA ⊢ oneCorrectSentence bit bitGraph) :
    M↓[language] ⊧ graphSentence (insertCode bit) := by
  simp only [models_iff, graphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      graphRew (insertCode bit) ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (insertCode bit) ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (insertCode bit)
        (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      graphRew (insertCode bit) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelInsertCode bit hb hc (e 0) (e 1)
end models

theorem PRA_has_insertCode : ∃ c : Code 2, PRA ⊢ graphSentence c := by
  have h : Hierarchy 𝚺 0 bitGraph := ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit,_,hb,hc⟩ := PRA_proves_boundedBooleanCharacteristic bitGraph h
  refine ⟨insertCode bit, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelGraphSentence bit hb hc
end DiophantineConsistency.PRAHistoryInsertCode
