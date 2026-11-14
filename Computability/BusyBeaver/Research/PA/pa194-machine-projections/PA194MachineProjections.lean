import PA194TargetCantor
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194MachineProjections
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAHerbrandSelection PRABoundedWitness PA194PathIterator PA194NumeralCode PA194TargetCantor
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def firstMatrix : Semisentence language 2 := Semiformula.lMap embedding firstDef.val
def secondMatrix : Semisentence language 2 := Semiformula.lMap embedding secondDef.val

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

theorem modelFirstTotal : M↓[language] ⊧ (∀⁰* ∃⁰ firstMatrix) := by
  simp only [models_iff,Semiformula.eval_allClosure,Semiformula.eval_ex]
  intro e
  refine ⟨first (e 0), ?_⟩
  rw [firstMatrix,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  have hv : (first (e 0) :> e) = ![first (e 0),e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv]
  exact (first_defined (V := M)).defined ![first (e 0),e 0] |>.mpr rfl

theorem modelSecondTotal : M↓[language] ⊧ (∀⁰* ∃⁰ secondMatrix) := by
  simp only [models_iff,Semiformula.eval_allClosure,Semiformula.eval_ex]
  intro e
  refine ⟨second (e 0), ?_⟩
  rw [secondMatrix,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  have hv : (second (e 0) :> e) = ![second (e 0),e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv]
  exact (second_defined (V := M)).defined ![second (e 0),e 0] |>.mpr rfl

theorem modelFirstSelected (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt firstMatrix f) (p : M) :
    F f ![p] = first p := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff,Semiformula.eval_allClosure] at hm
  have hm := hm ![p]
  rw [PRAHerbrandSelection.openMatrixAt,Semiformula.eval_substs] at hm
  have hv : (Semiterm.val (L := language) ![p] Empty.elim ∘
      Fin.cases (PRATheory.applyCode f (PRATheory.vars 1)) (PRATheory.vars 1)) = ![F f ![p],p] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change F f (Semiterm.val (L := language) ![p] Empty.elim ∘ PRATheory.vars 1) = _
      congr 1
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv,firstMatrix,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hm
  exact ((first_defined (V := M)).defined ![F f ![p],p]).mp hm

theorem modelSecondSelected (f : Code 1)
    (h : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt secondMatrix f) (p : M) :
    F f ![p] = second p := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff,Semiformula.eval_allClosure] at hm
  have hm := hm ![p]
  rw [PRAHerbrandSelection.openMatrixAt,Semiformula.eval_substs] at hm
  have hv : (Semiterm.val (L := language) ![p] Empty.elim ∘
      Fin.cases (PRATheory.applyCode f (PRATheory.vars 1)) (PRATheory.vars 1)) = ![F f ![p],p] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change F f (Semiterm.val (L := language) ![p] Empty.elim ∘ PRATheory.vars 1) = _
      congr 1
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv,secondMatrix,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard] at hm
  exact ((second_defined (V := M)).defined ![F f ![p],p]).mp hm
end models

theorem PRA_has_firstCode : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt firstMatrix f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy firstDef.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelFirstTotal

theorem PRA_has_secondCode : ∃ f : Code 1, Primrec (eval f) ∧
    PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt secondMatrix f := by
  apply PRA_boundedWitness
  · exact ParsonsHierarchyMap.hierarchy secondDef.sigma_prop
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelSecondTotal

noncomputable def fixedFirst : Code 1 := Classical.choose PRA_has_firstCode
noncomputable def fixedSecond : Code 1 := Classical.choose PRA_has_secondCode

theorem fixedFirst_certified : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt firstMatrix fixedFirst :=
  (Classical.choose_spec PRA_has_firstCode).2
theorem fixedSecond_certified : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt secondMatrix fixedSecond :=
  (Classical.choose_spec PRA_has_secondCode).2

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

theorem fixedFirst_model (p : M) : F fixedFirst ![p] = first p :=
  modelFirstSelected fixedFirst fixedFirst_certified p
theorem fixedSecond_model (p : M) : F fixedSecond ![p] = second p :=
  modelSecondSelected fixedSecond fixedSecond_certified p

theorem first_machinePair (a b : M) : F fixedFirst ![F fixedCantor ![a,b]] = a := by
  rw [fixedFirst_model,modelCantorSelected fixedCantor fixedCantor_certified,first_cantor]
theorem second_machinePair (a b : M) : F fixedSecond ![F fixedCantor ![a,b]] = b := by
  rw [fixedSecond_model,modelCantorSelected fixedCantor fixedCantor_certified,second_cantor]

#print axioms fixedFirst_model
#print axioms fixedSecond_model
#print axioms first_machinePair
#print axioms second_machinePair
end models
end PA194MachineProjections
