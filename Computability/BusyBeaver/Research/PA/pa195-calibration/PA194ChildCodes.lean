import PA195DecodedFields
import DiophantineConsistency.PRABoundedWitness

/-! Candidate-PRA witness codes for the exact PA194 decoder children. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194ChildCodes
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAModelIOpenPairing PRABoundedWitness

abbrev firstGraph := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.firstDef
abbrev secondGraph := SetTheory.BusyBeaver.ZFC.ArithmeticCantor.secondDef

def firstMatrix : 𝚺₀.Semisentence 2 := .mkSigma
  “a n. ∃ p <⁺ n, !divDef p n 4 ∧ !firstGraph a p”

def secondMatrix : 𝚺₀.Semisentence 2 := .mkSigma
  “b n. ∃ p <⁺ n, !divDef p n 4 ∧ !secondGraph b p”

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem firstMatrix_eval (a n : M) : firstMatrix.val.Evalb ![a,n] ↔ a = first (n / 4) := by
  have hd (p : M) : divDef.val.Evalb ![p,n,4] ↔ p = n / 4 := by
    simp [divDef, div_graph, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.def_of_Eq_of_LT,
      le_iff_eq_or_lt]
  have hf (a p : M) : firstGraph.val.Evalb ![a,p] ↔ a = first p := by simp [firstGraph]
  simp [firstMatrix, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hd, hf]

theorem secondMatrix_eval (b n : M) : secondMatrix.val.Evalb ![b,n] ↔ b = second (n / 4) := by
  have hd (p : M) : divDef.val.Evalb ![p,n,4] ↔ p = n / 4 := by
    simp [divDef, div_graph, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.def_of_Eq_of_LT,
      le_iff_eq_or_lt]
  have hs (b p : M) : secondGraph.val.Evalb ![b,p] ↔ b = second p := by simp [secondGraph]
  simp [secondMatrix, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hd, hs]

theorem modelFirstTotal : M↓[language] ⊧ (∀⁰* ∃⁰ Semiformula.lMap embedding firstMatrix.val) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  refine ⟨first (e 0 / 4), ?_⟩
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have he : (first (e 0 / 4) :> e) = ![first (e 0 / 4),e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he, firstMatrix_eval]

theorem modelSecondTotal : M↓[language] ⊧ (∀⁰* ∃⁰ Semiformula.lMap embedding secondMatrix.val) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex]
  intro e
  refine ⟨second (e 0 / 4), ?_⟩
  rw [Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  have he : (second (e 0 / 4) :> e) = ![second (e 0 / 4),e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [he, secondMatrix_eval]

/-- A candidate-PRA graph witness evaluates to its represented arithmetic
relation at every model element. -/
theorem modelSelected (φ : ArithmeticSemisentence 2) (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding φ) f)
    (n : M) :
    φ.Evalb ![Structure.func (L := language) f (fun _ => n),n] := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, Semiformula.eval_allClosure] at hm
  have hm := hm ![n]
  rw [PRAHerbrandSelection.openMatrixAt, Semiformula.eval_substs] at hm
  have hv : (Semiterm.val (L := language) ![n] Empty.elim ∘
      Fin.cases (PRATheory.applyCode f (PRATheory.vars 1)) (PRATheory.vars 1)) =
      ![Structure.func (L := language) f (fun _ => n),n] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) f
        (Semiterm.val (L := language) ![n] Empty.elim ∘ PRATheory.vars 1) = _
      congr 1
      funext j
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv, Semiformula.eval_lMap, PRAModelIOpenPairing.reduct_eq_standard] at hm
  exact hm

theorem modelFirstCode (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding firstMatrix.val) f)
    (n : M) : Structure.func (L := language) f (fun _ => n) = first (n / 4) :=
  (firstMatrix_eval _ n).mp (modelSelected firstMatrix.val f h n)

theorem modelSecondCode (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding secondMatrix.val) f)
    (n : M) : Structure.func (L := language) f (fun _ => n) = second (n / 4) :=
  (secondMatrix_eval _ n).mp (modelSelected secondMatrix.val f h n)

end models

/-- The exact first and second decoder-child graphs have candidate-PRA
primitive-recursive witness codes. This does not yet construct arbitrary
branch-selected paths or connect them to recursive occurrence. -/
theorem PRA_has_firstChildCode : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding firstMatrix.val) f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy firstMatrix.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelFirstTotal

theorem PRA_has_secondChildCode : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt (Semiformula.lMap embedding secondMatrix.val) f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy secondMatrix.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelSecondTotal

#print axioms modelFirstCode
#print axioms modelSecondCode
#print axioms PRA_has_firstChildCode
#print axioms PRA_has_secondChildCode
#print axioms firstMatrix_eval
#print axioms secondMatrix_eval
end PA194ChildCodes
