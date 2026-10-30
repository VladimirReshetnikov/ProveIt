import DiophantineConsistency.PRAHistoryFixpointCollector
import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryFixpointSuccCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryFixpointCollector
  PRACharacteristicBit PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness

noncomputable def sigmaCore (φ : Fixpoint.Blueprint 0) : Semisentence language 2 :=
  Semiformula.lMap embedding φ.core.sigma.val
noncomputable def piCore (φ : Fixpoint.Blueprint 0) : Semisentence language 2 :=
  Semiformula.lMap embedding φ.core.pi.val

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelFixSuccValue (good ins : Code 2) (ih s : M) :
    Structure.func (L := language) (fixSuccCode good ins) ![ih,s] =
      Structure.func (L := language) (collectCode good ins)
        ![Structure.func (L := language) Code.succ (fun _ => s),ih] := by
  rw [fixSuccCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Structure.func (L := language) (Code.comp Code.succ (.cons (.proj 1) (.nil 2)))
      ![ih,s] = Structure.func (L := language) Code.succ (fun _ => s)
    rw [modelComposition]
    congr 1
    funext j
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact modelProjection 1 ![ih,s]
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) (.proj 0) ![ih,s] = ih
    exact modelProjection 0 ![ih,s]

theorem modelFixSuccMembership (good ins bit : Code 2)
    (hbit : PRA ⊢ bitSentence good) (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hcorrect : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (k ih s : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
      have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
      rw [PRAModelIOpenPairing.reduct_eq_standard] at h
      exact h
    bitDef.val.Evalb ![k,Structure.func (L := language) (fixSuccCode good ins) ![ih,s]] ↔
      k ≤ s ∧ Structure.func (L := language) good ![k,ih] =
        Structure.func (L := language) oneCode Fin.elim0 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  rw [modelFixSuccValue,modelCollectInvariant good ins bit hbit hins hcorrect]
  rw [←modelAddOne]
  change (k < s+1 ∧ _) ↔ _
  rw [lt_succ_iff_le]
theorem modelFixSuccGraph (φ : Fixpoint.Blueprint 0) (good ins bit : Code 2)
    (hbit : PRA ⊢ bitSentence good) (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbitCorrect : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (hsigma : PRA ⊢ oneCorrectSentence good (sigmaCore φ))
    (hpi : PRA ⊢ oneCorrectSentence good (piCore φ)) (ih s : M) :
    (Semiformula.lMap embedding φ.succDef.val).Eval
      ![Structure.func (L := language) (fixSuccCode good ins) ![ih,s],ih,s] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  let u := Structure.func (L := language) (fixSuccCode good ins) ![ih,s]
  have core (ψ : Semisentence language 2) (hc : PRA ⊢ oneCorrectSentence good ψ) (x : M) :
      Structure.func (L := language) good ![x,ih] = Structure.func (L := language) oneCode Fin.elim0 ↔
        ψ.Eval ![x,ih] Empty.elim := by
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
    have h := modelCharacteristicMatrix good ψ hm ![x,ih]
    have hz : (Semiterm.val (L := language) ![x,ih] Empty.elim ∘ Fin.elim0) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    have hv : (Semiterm.val (L := language) ![x,ih] Empty.elim ∘ vars 2) = ![x,ih] := by
      funext j
      refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
    simpa [characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode,
      Semiterm.val_func, hz, hv] using h
  have hs (x : M) : Structure.func (L := language) good ![x,ih] =
      Structure.func (L := language) oneCode Fin.elim0 ↔ φ.core.sigma.val.Evalb ![x,ih] := by
    have h := core (sigmaCore φ) hsigma x
    rw [sigmaCore, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  have hp (x : M) : Structure.func (L := language) good ![x,ih] =
      Structure.func (L := language) oneCode Fin.elim0 ↔ φ.core.pi.val.Evalb ![x,ih] := by
    have h := core (piCore φ) hpi x
    rw [piCore, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp [Fixpoint.Blueprint.succDef, Semiformula.ballLT, FirstOrder.ball,
    Semiformula.Operator.val, operator_mem_def, Semiformula.Operator.LE.def_of_Eq_of_LT,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]
  intro x hx
  have hm := modelFixSuccMembership good ins bit hbit hins hbitCorrect x ih s
  constructor
  · intro hb
    have hh := hm.mp hb
    exact ⟨hh.1,(hs x).mp hh.2⟩
  · intro hle hc
    exact hm.mpr ⟨hle,(hp x).mpr hc⟩
def graphRew (c : Code 2) : Rew language Empty 3 Empty 2 := Rew.embSubsts
  ![.func c ![#0,#1],#0,#1]

noncomputable def graphSentence (φ : Fixpoint.Blueprint 0) (c : Code 2) : Sentence language := ∀⁰*
  (graphRew c ▹ Semiformula.lMap embedding φ.succDef.val)

theorem modelGraphSentence (φ : Fixpoint.Blueprint 0) (good ins bit : Code 2)
    (hbit : PRA ⊢ bitSentence good) (hins : PRA ⊢ PRAHistoryInsertCode.graphSentence ins)
    (hbitCorrect : PRA ⊢ oneCorrectSentence bit PRAHistoryInsertCode.bitGraph)
    (hsigma : PRA ⊢ oneCorrectSentence good (sigmaCore φ))
    (hpi : PRA ⊢ oneCorrectSentence good (piCore φ)) :
    M↓[language] ⊧ graphSentence φ (fixSuccCode good ins) := by
  simp only [models_iff, graphSentence, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      graphRew (fixSuccCode good ins) ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (fixSuccCode good ins) ![e 0,e 1],e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (fixSuccCode good ins)
        (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      graphRew (fixSuccCode good ins) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelFixSuccGraph φ good ins bit hbit hins hbitCorrect hsigma hpi (e 0) (e 1)
end models

theorem PRA_has_fixSuccCode (φ : Fixpoint.Blueprint 0) (good : Code 2)
    (hbit : PRA ⊢ bitSentence good)
    (hsigma : PRA ⊢ oneCorrectSentence good (sigmaCore φ))
    (hpi : PRA ⊢ oneCorrectSentence good (piCore φ)) :
    ∃ c : Code 2, PRA ⊢ graphSentence φ c := by
  obtain ⟨ins,hins⟩ := PRAHistoryInsertCode.PRA_has_insertCode
  have h : Hierarchy 𝚺 0 PRAHistoryInsertCode.bitGraph :=
    ParsonsHierarchyMap.hierarchy bitDef.sigma_prop
  obtain ⟨bit,_,_,hbitCorrect⟩ := PRA_proves_boundedBooleanCharacteristic PRAHistoryInsertCode.bitGraph h
  refine ⟨fixSuccCode good ins, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelGraphSentence φ good ins bit hbit hins hbitCorrect hsigma hpi
end DiophantineConsistency.PRAHistoryFixpointSuccCode
