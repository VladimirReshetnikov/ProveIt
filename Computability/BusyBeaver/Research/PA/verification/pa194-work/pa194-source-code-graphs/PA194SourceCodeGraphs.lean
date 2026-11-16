import PA194SearchPRACode
import PA194SeqDepthPRACode
import PA194CodeGraph
/-! Fixed Σ₁ graphs for the source operations: model interpretation only. -/
set_option autoImplicit false
namespace PA194SourceCodeGraphs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA194SourcePRACodes PA194SearchPRACode PA194SeqDepthPRACode
open PA194FormulaShiftPR PA194BudgetSkeleton PA194DepthPR

noncomputable def shiftCode : Code 1 := Classical.choose shift_has_PRA_code
noncomputable def depthCode : Code 1 := Classical.choose depth_has_PRA_code
noncomputable def budgetCode : Code 1 := Classical.choose budget_has_PRA_code
noncomputable def searchCode : Code 2 := Classical.choose search_has_PRA_code
noncomputable def sequentDepthCode : Code 1 := Classical.choose (unaryCode_of_primrec _ numericSequentDepth_primrec)

theorem shift_standard : ∀ n, eval shiftCode (List.Vector.ofFn (fun _ : Fin 1 => n)) = formulaShiftCode n :=
  Classical.choose_spec shift_has_PRA_code
theorem depth_standard : ∀ n, eval depthCode (List.Vector.ofFn (fun _ : Fin 1 => n)) = PA194DepthPR.depthCode n :=
  Classical.choose_spec depth_has_PRA_code
theorem budget_standard : ∀ n, eval budgetCode (List.Vector.ofFn (fun _ : Fin 1 => n)) = PA194BudgetSkeleton.budgetCode n :=
  Classical.choose_spec budget_has_PRA_code
theorem search_standard : ∀ s q, eval searchCode (List.Vector.ofFn (fun i : Fin 2 => if i = 0 then s else q)) = numericSearch s q :=
  Classical.choose_spec search_has_PRA_code
theorem sequentDepth_standard : ∀ n, eval sequentDepthCode (List.Vector.ofFn (fun _ : Fin 1 => n)) = numericSequentDepth n :=
  Classical.choose_spec (unaryCode_of_primrec _ numericSequentDepth_primrec)

noncomputable def shiftGraph : 𝚺₁.Semisentence 2 := PA194CodeGraph.graph shiftCode
noncomputable def depthGraph : 𝚺₁.Semisentence 2 := PA194CodeGraph.graph depthCode
noncomputable def budgetGraph : 𝚺₁.Semisentence 2 := PA194CodeGraph.graph budgetCode
noncomputable def searchGraph : 𝚺₁.Semisentence 3 := PA194CodeGraph.graph searchCode
noncomputable def sequentDepthGraph : 𝚺₁.Semisentence 2 := PA194CodeGraph.graph sequentDepthCode

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shift_defined : 𝚺₁.DefinedFunction (fun e : Fin 1 → M => F shiftCode e) shiftGraph :=
  PA194CodeGraph.modelGraph shiftCode
theorem depth_defined : 𝚺₁.DefinedFunction (fun e : Fin 1 → M => F depthCode e) depthGraph :=
  PA194CodeGraph.modelGraph depthCode
theorem budget_defined : 𝚺₁.DefinedFunction (fun e : Fin 1 → M => F budgetCode e) budgetGraph :=
  PA194CodeGraph.modelGraph budgetCode
theorem search_defined : 𝚺₁.DefinedFunction (fun e : Fin 2 → M => F searchCode e) searchGraph :=
  PA194CodeGraph.modelGraph searchCode
theorem sequentDepth_defined : 𝚺₁.DefinedFunction (fun e : Fin 1 → M => F sequentDepthCode e) sequentDepthGraph :=
  PA194CodeGraph.modelGraph sequentDepthCode
#print axioms shift_defined
#print axioms depth_defined
#print axioms budget_defined
#print axioms search_defined
#print axioms sequentDepth_defined
end models
#print axioms shift_standard
#print axioms search_standard
end PA194SourceCodeGraphs
