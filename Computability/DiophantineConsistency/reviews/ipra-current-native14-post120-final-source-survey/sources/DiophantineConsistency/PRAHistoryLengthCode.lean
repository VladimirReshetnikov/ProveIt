import DiophantineConsistency.PRABoundedWitness
import DiophantineConsistency.PRAModelIOpenPairing
import Foundation.FirstOrder.Arithmetic.HFS.Seq
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryLengthCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABoundedWitness
  PRAModelIOpenPairing

set_option maxHeartbeats 2000000 in
theorem length_total {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (s : V) :
    ∃ l ≤ 2*s, lhDef.val.Evalb ![l,s] := by
  by_cases hs : seqDef.val.Evalb ![s]
  · have hh := hs
    simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le] at hh
    obtain ⟨_,l,hl,d,hd,hdomain,hunder⟩ := hh
    refine ⟨l,hl,?_⟩
    simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs]
    exact ⟨d,hd,hdomain,hunder⟩
  · refine ⟨0,by simp,?_⟩
    simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs]

def lhMatrix : 𝚺₀.Semisentence 2 := .mkSigma
  “l s. l < 2*s+1 ∧ !lhDef l s”

def mappedMatrix : Semisentence language 2 := Semiformula.lMap embedding lhMatrix.val

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelTotal : M↓[language] ⊧ (∀⁰* ∃⁰ mappedMatrix) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  obtain ⟨l,hl,hgraph⟩ := length_total (e 0)
  refine ⟨l,?_⟩
  rw [mappedMatrix, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have he : (l :> e) = ![l,e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he]
  simpa [lhMatrix, Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq,
    lt_succ_iff_le] using And.intro hl hgraph
end models

theorem PRA_proves_total : PRA ⊢ (∀⁰* ∃⁰ mappedMatrix) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelTotal

theorem PRA_has_lengthCode : ∃ w : Code 1, Primrec (eval w) ∧
    PRA ⊢ (∀⁰* PRAHerbrandSelection.openMatrixAt mappedMatrix w) := by
  apply PRA_boundedWitness mappedMatrix
  · exact ParsonsHierarchyMap.hierarchy lhMatrix.sigma_prop
  · exact PRA_proves_total
end DiophantineConsistency.PRAHistoryLengthCode
