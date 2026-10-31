import DiophantineConsistency.PRAHistoryFixpointSuccCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryTermCoreCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRACharacteristicBit
  PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def termCoreBounded : 𝚺₀.Semisentence 2 := .mkSigma
  “t C. (∃ z < t, !qqBvarDef t z) ∨ (∃ x < t, !qqFvarDef t x)”
noncomputable def mappedBounded : Semisentence language 2 := Semiformula.lMap embedding termCoreBounded.val
noncomputable def sigmaCore : Semisentence language 2 := Semiformula.lMap embedding
  (FormalizedTerm.blueprint L).core.sigma.val
noncomputable def piCore : Semisentence language 2 := Semiformula.lMap embedding
  (FormalizedTerm.blueprint L).core.pi.val

set_option maxHeartbeats 2000000 in
theorem termCore_sigma_eval (hL : L.isFunc.val = ⊥) {V : Type} [ORingStructure V] (t C : V) :
    (FormalizedTerm.blueprint L).core.sigma.val.Evalb ![t,C] ↔ termCoreBounded.val.Evalb ![t,C] := by
  simp [FormalizedTerm.blueprint, termCoreBounded, hL]

set_option maxHeartbeats 2000000 in
theorem termCore_pi_eval (hL : L.isFunc.val = ⊥) {V : Type} [ORingStructure V] (t C : V) :
    (FormalizedTerm.blueprint L).core.pi.val.Evalb ![t,C] ↔ termCoreBounded.val.Evalb ![t,C] := by
  simp [FormalizedTerm.blueprint, termCoreBounded, hL]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [M↓[language] ⊧* PRA] in
theorem modelSigmaEquiv (hL : L.isFunc.val = ⊥) (e : Fin 2 → M) :
    (mappedBounded).Eval e Empty.elim ↔ (sigmaCore (L := L)).Eval e Empty.elim := by
  rw [mappedBounded, sigmaCore, Semiformula.eval_lMap, Semiformula.eval_lMap,
    PRAModelIOpenPairing.reduct_eq_standard, Matrix.fun_eq_vec_two e]
  exact (termCore_sigma_eval hL (e 0) (e 1)).symm

omit [M↓[language] ⊧* PRA] in
theorem modelPiEquiv (hL : L.isFunc.val = ⊥) (e : Fin 2 → M) :
    (mappedBounded).Eval e Empty.elim ↔ (piCore (L := L)).Eval e Empty.elim := by
  rw [mappedBounded, piCore, Semiformula.eval_lMap, Semiformula.eval_lMap,
    PRAModelIOpenPairing.reduct_eq_standard, Matrix.fun_eq_vec_two e]
  exact (termCore_pi_eval hL (e 0) (e 1)).symm
end models

theorem PRA_has_termCoreCode (hL : L.isFunc.val = ⊥) :
    ∃ c : Code 2, PRA ⊢ bitSentence c ∧
      PRA ⊢ oneCorrectSentence c (sigmaCore (L := L)) ∧
      PRA ⊢ oneCorrectSentence c (piCore (L := L)) := by
  obtain ⟨c,_,hbit,hcore⟩ := PRA_proves_boundedBooleanCharacteristic (mappedBounded)
    (ParsonsHierarchyMap.hierarchy termCoreBounded.sigma_prop)
  refine ⟨c,hbit,?_,?_⟩
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    apply (oneCorrectSentence_iff c (sigmaCore (L := L))).mpr
    intro e
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcore
    exact ((oneCorrectSentence_iff c (mappedBounded)).mp hm e).trans (modelSigmaEquiv hL e)
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    apply (oneCorrectSentence_iff c (piCore (L := L))).mpr
    intro e
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcore
    exact ((oneCorrectSentence_iff c (mappedBounded)).mp hm e).trans (modelPiEquiv hL e)

theorem PRA_has_termSuccCode (hL : L.isFunc.val = ⊥) :
    ∃ c : Code 2, PRA ⊢ PRAHistoryFixpointSuccCode.graphSentence (FormalizedTerm.blueprint L) c := by
  obtain ⟨good,hbit,hsigma,hpi⟩ := PRA_has_termCoreCode (L := L) hL
  exact PRAHistoryFixpointSuccCode.PRA_has_fixSuccCode (FormalizedTerm.blueprint L) good hbit hsigma hpi
end DiophantineConsistency.PRAHistoryTermCoreCode
