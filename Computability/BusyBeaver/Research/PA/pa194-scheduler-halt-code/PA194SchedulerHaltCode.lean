import PA194SchedulerToPA
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SchedulerHaltCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PA194PathIterator
 PA194TargetCantor PA194TargetGate PA194TargetProofLeaf PA194SchedulerIteration PA194SchedulerToPA PA194SourceLineSoundness

/-- One fixed unary PRA code evaluates the modeled halt bit after a specified
number of iterations from the modeled initial scheduler state. -/
noncomputable def initialConstant : Code 1 := .comp initial (.nil 1)
noncomputable def haltAfter : Code 1 := unary haltAt (bin run (.proj 0) initialConstant)

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

theorem initialConstant_model (e : Fin 1 → M) : F initialConstant e = F initial Fin.elim0 := by
  rw [initialConstant,modelComposition]
  congr 1
  exact Subsingleton.elim _ _

theorem haltAfter_model (k : M) :
    F haltAfter ![k] = F haltAt ![F run ![k,F initial Fin.elim0]] := by
  rw [haltAfter,modelUnary,modelBin,modelProjection,initialConstant_model]
  simp only [Matrix.cons_val_zero]
  have hv (v : M) : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]

theorem modeled_halt_provable (k : M) (hh : F haltAfter ![k] = 1) : TargetProvable (1 : M) := by
  rw [haltAfter_model] at hh
  exact initial_run_halt_provable k hh

theorem modeled_halt_refutes_PA
    (hgate : ∀ a b c : M, c ≠ a → c ≠ b → good (oldBundleValue a b c))
    (k : M) (hh : F haltAfter ![k] = 1) : Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  rw [haltAfter_model] at hh
  exact PA194SchedulerToPA.modeled_halt_refutes_PA hgate k hh

theorem modeled_halt_refutes_PA_of_tail
    (htail : ∀ a b c : M, c ≠ a → c ≠ b →
      good (PA194SourceGateReduction.gateNeg (separationTailValue a b c)))
    (k : M) (hh : F haltAfter ![k] = 1) : Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  rw [haltAfter_model] at hh
  exact PA194SchedulerToPA.modeled_halt_refutes_PA_of_tail htail k hh

theorem haltAfter_graph : 𝚺₁.DefinedFunction
    (fun e : Fin 1 → M => F haltAfter e) (PA194CodeGraph.graph haltAfter) :=
  PA194CodeGraph.modelGraph haltAfter

#print axioms haltAfter_model
#print axioms modeled_halt_provable
#print axioms modeled_halt_refutes_PA
#print axioms modeled_halt_refutes_PA_of_tail
#print axioms haltAfter_graph
end models
end PA194SchedulerHaltCode
