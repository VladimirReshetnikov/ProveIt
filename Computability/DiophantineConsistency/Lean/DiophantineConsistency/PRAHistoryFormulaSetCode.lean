import DiophantineConsistency.PRAHistoryFixpointCollector
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryFormulaSetCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRACharacteristicBit
  PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness

def scanBitRew : Rew language Empty 2 Empty 2 := Rew.embSubsts ![#0,#1]
def scanGood (good : Code 2) : Semisentence language 2 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func good ![.func (Code.zero 0) Fin.elim0,#0],.func oneCode Fin.elim0]
def scan (good : Code 2) : Semisentence language 1 :=
  ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0,#1])]
    ((scanBitRew ▹ PRAHistoryInsertCode.bitGraph) 🡒 scanGood good)

theorem scan_bounded (good : Code 2) : Hierarchy 𝚺 0 (scan good) := by
  unfold scan scanGood
  apply Hierarchy.ball
  · simp [Semiterm.Positive]
  · apply Hierarchy.imp_iff.mpr
    constructor
    · exact Hierarchy.zero_eq_alt (Hierarchy.rew _ (ParsonsHierarchyMap.hierarchy bitDef.sigma_prop))
    · simp

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem scan_eval (good : Code 2) (s : M) : (scan good).Eval ![s] Empty.elim ↔
    ∀ p : M, Structure.rel (L := language) Language.ORing.Rel.lt ![p,s] →
      (PRAHistoryInsertCode.bitGraph.Eval ![p,s] Empty.elim →
        Structure.func (L := language) good
          ![Structure.func (L := language) (Code.zero 0) Fin.elim0,p] =
          Structure.func (L := language) oneCode Fin.elim0) := by
  simp only [scan, FirstOrder.ball, Semiformula.eval_all]
  apply forall_congr'
  intro p
  have hz : (Semiterm.val (L := language) ![p,s] Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) ![p,s] Empty.elim ∘ scanBitRew ∘ Semiterm.bvar) = ![p,s] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![p,s] Empty.elim ∘ scanBitRew ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp [scanGood, Semiformula.eval_rel, Semiformula.eval_rew, eqRel, Semiterm.val_func, hz,hv,he]
end models

variable {L : Language} [L.Encodable] [L.LORDefinable]
noncomputable def semiSigma : Semisentence language 2 :=
  Semiformula.lMap embedding (isSemiformula L).sigma.val
noncomputable def semiPi : Semisentence language 2 :=
  Semiformula.lMap embedding (isSemiformula L).pi.val
noncomputable def setSigma : Semisentence language 1 :=
  Semiformula.lMap embedding (isFormulaSet L).sigma.val
noncomputable def setPi : Semisentence language 1 :=
  Semiformula.lMap embedding (isFormulaSet L).pi.val

set_option maxHeartbeats 2000000 in
theorem formulaSet_sigma_eval {V : Type} [ORingStructure V] (s : V) :
    (isFormulaSet L).sigma.val.Evalb ![s] ↔
      ∀ p < s, bitDef.val.Evalb ![p,s] → (isSemiformula L).sigma.val.Evalb ![0,p] := by
  simp [isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball,
    Semiformula.Operator.val, operator_mem_def, Semiformula.Operator.LT.sentence_eq]

set_option maxHeartbeats 2000000 in
theorem formulaSet_pi_eval {V : Type} [ORingStructure V] (s : V) :
    (isFormulaSet L).pi.val.Evalb ![s] ↔
      ∀ p < s, bitDef.val.Evalb ![p,s] → (isSemiformula L).pi.val.Evalb ![0,p] := by
  simp [isFormulaSet, ballIn, Semiformula.ballLT, FirstOrder.ball,
    Semiformula.Operator.val, operator_mem_def, Semiformula.Operator.LT.sentence_eq]

section transfer
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelScanSigma (good : Code 2) (hc : PRA ⊢ oneCorrectSentence good (semiSigma (L := L))) (s : M) :
    (scan good).Eval ![s] Empty.elim ↔ (setSigma (L := L)).Eval ![s] Empty.elim := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
  have hm := (oneCorrectSentence_iff good (semiSigma (L := L))).mp hm
  rw [scan_eval, setSigma, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard,
    formulaSet_sigma_eval]
  apply forall_congr'
  intro p
  have hh := hm ![0,p]
  rw [semiSigma, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hh
  have hb : PRAHistoryInsertCode.bitGraph.Eval ![p,s] Empty.elim ↔ bitDef.val.Evalb ![p,s] := by
    rw [PRAHistoryInsertCode.bitGraph,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  change (p < s → (PRAHistoryInsertCode.bitGraph.Eval ![p,s] Empty.elim → _)) ↔ _
  rw [hb]
  change (p < s → bitDef.val.Evalb ![p,s] →
    Structure.func (L := language) good ![(0 : M),p] = Structure.func (L := language) oneCode Fin.elim0) ↔ _
  rw [hh]

theorem modelScanPi (good : Code 2) (hc : PRA ⊢ oneCorrectSentence good (semiPi (L := L))) (s : M) :
    (scan good).Eval ![s] Empty.elim ↔ (setPi (L := L)).Eval ![s] Empty.elim := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
  have hm := (oneCorrectSentence_iff good (semiPi (L := L))).mp hm
  rw [scan_eval, setPi, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard,
    formulaSet_pi_eval]
  apply forall_congr'
  intro p
  have hh := hm ![0,p]
  rw [semiPi, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hh
  have hb : PRAHistoryInsertCode.bitGraph.Eval ![p,s] Empty.elim ↔ bitDef.val.Evalb ![p,s] := by
    rw [PRAHistoryInsertCode.bitGraph,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  change (p < s → (PRAHistoryInsertCode.bitGraph.Eval ![p,s] Empty.elim → _)) ↔ _
  rw [hb]
  change (p < s → bitDef.val.Evalb ![p,s] →
    Structure.func (L := language) good ![(0 : M),p] = Structure.func (L := language) oneCode Fin.elim0) ↔ _
  rw [hh]
end transfer

theorem PRA_has_formulaSetCode (good : Code 2)
    (hsigma : PRA ⊢ oneCorrectSentence good (semiSigma (L := L)))
    (hpi : PRA ⊢ oneCorrectSentence good (semiPi (L := L))) :
    ∃ c : Code 1, PRA ⊢ bitSentence c ∧
      PRA ⊢ oneCorrectSentence c (setSigma (L := L)) ∧
      PRA ⊢ oneCorrectSentence c (setPi (L := L)) := by
  obtain ⟨c,_,hbit,hscan⟩ := PRA_proves_boundedBooleanCharacteristic (scan good) (scan_bounded good)
  refine ⟨c,hbit,?_,?_⟩
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    apply (oneCorrectSentence_iff c (setSigma (L := L))).mpr
    intro e
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hscan
    have h := (oneCorrectSentence_iff c (scan good)).mp hm e
    rw [Matrix.fun_eq_vec_one e] at h ⊢
    exact h.trans (modelScanSigma good hsigma (e 0))
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    apply (oneCorrectSentence_iff c (setPi (L := L))).mpr
    intro e
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hscan
    have h := (oneCorrectSentence_iff c (scan good)).mp hm e
    rw [Matrix.fun_eq_vec_one e] at h ⊢
    exact h.trans (modelScanPi good hpi (e 0))
end DiophantineConsistency.PRAHistoryFormulaSetCode
