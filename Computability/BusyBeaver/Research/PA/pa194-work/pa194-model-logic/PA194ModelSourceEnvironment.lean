import PA194ModelSourceAtomCode

/-! Model-level environment transition at a source binder. The stack update has
exactly the head/tail behavior of extending the bound-label map by `Fin.cases`.
This is not yet a compiler for internal source-formula codes. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- Prepend a new bound-variable label to the encoded environment. -/
def pushBound : Code 2 := unary .succ (bin pairCode (.proj 0) (.proj 1))

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

theorem pushBound_model (new old : M) :
    F pushBound ![new,old] = pair new old+1 := by
  simp only [pushBound,modelUnary,modelBin,modelProjection,modelSucc,modelPairCode,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.vecHead,Matrix.vecTail,Function.comp_def]

theorem binder_bound_zero (new old free : M) :
    F termLabelCode ![^#(0 : M),pair new old+1,free] = new := by
  rw [termLabel_bound]
  exact modelLookupZero firstProjection secondProjection firstProjection_certified _ _

theorem binder_bound_succ (new old free i : M) :
    F termLabelCode ![^#(i+1),pair new old+1,free] = F termLabelCode ![^#i,old,free] := by
  rw [termLabel_bound,termLabel_bound]
  exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified _ _ _

theorem binder_free (new old free i : M) :
    F termLabelCode ![^&i,pair new old+1,free] = F termLabelCode ![^&i,old,free] := by
  rw [termLabel_free,termLabel_free]

#print axioms pushBound_model
#print axioms binder_bound_zero
#print axioms binder_bound_succ
#print axioms binder_free
end models
end PA194ModelLogic
