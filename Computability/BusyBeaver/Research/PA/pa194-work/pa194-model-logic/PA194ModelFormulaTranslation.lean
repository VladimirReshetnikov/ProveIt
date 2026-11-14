import PA194ModelFormulaSpecification

/-! A fixed finite candidate-PRA root code for the source-to-numerical syntactic
translation. Agreement with an independent Σ₁ structural recursion covers
nonstandard source codes, but is not a freshness or semantic-soundness theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- Inputs: source formula, initial bound stack, free stack, first binder label,
and reserved neighborhood label. The root budget is the source formula code. -/
noncomputable def fixedFormulaTranslation : Code 5 :=
  applyFour formulaHistory (.proj 0) (.proj 0)
    (bin pairCode (.proj 1) (.proj 2))
    (bin pairCode (.proj 0) (bin pairCode (.proj 3) (.proj 4)))

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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixedFormulaTranslation_model (p bound free base reserve : M) :
    F fixedFormulaTranslation ![p,bound,free,base,reserve] =
      F formulaHistory ![p,p,pair bound free,pair p (pair base reserve)] := by
  simp only [fixedFormulaTranslation,applyFour_model,modelBin,modelPairCode,modelProjection,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

theorem fixedFormulaTranslation_correct (p bound free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F fixedFormulaTranslation ![p,bound,free,base,reserve] =
      formulaReference (pair bound free) (pair p (pair base reserve)) p p := by
  rw [fixedFormulaTranslation_model]
  exact formulaHistory_reference_root p (pair bound free) (pair p (pair base reserve)) hp

theorem fixedFormulaTranslation_graph (p bound free base reserve y : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    (PA194CodeGraph.graph fixedFormulaTranslation).val.Eval ![y,p,bound,free,base,reserve] Empty.elim ↔
      y = formulaReference (pair bound free) (pair p (pair base reserve)) p p := by
  have h := (PA194CodeGraph.modelGraph (M := M) fixedFormulaTranslation).defined ![y,p,bound,free,base,reserve]
  have he : (fun i : Fin 5 => ![y,p,bound,free,base,reserve] i.succ) = ![p,bound,free,base,reserve] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    refine Fin.cases rfl (fun m => ?_) l
    exact Fin.cases rfl (fun n => Fin.elim0 n) m
  simp only [Matrix.cons_val_zero] at h
  rw [he,fixedFormulaTranslation_correct p bound free base reserve hp] at h
  exact h

#print axioms fixedFormulaTranslation_model
#print axioms fixedFormulaTranslation_correct
#print axioms fixedFormulaTranslation_graph
end models
end PA194ModelLogic
