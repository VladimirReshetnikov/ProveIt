import PA194TargetGate
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetRho8
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable
 PA194NumeralCode PA194TargetCantor PA194TargetLeaves PA194TargetLeavesStandard

/-- Inputs `a,b,c,u`; zero rejects and successor of the formula accepts. -/
noncomputable def checkRho8 : Code 4 :=
  selectAmong (bin ltBitCode (.proj 0) (.proj 3)) (.zero 4) (unary .succ rho8)
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

theorem checkRho8_model (a b c u : M) : F checkRho8 ![a,b,c,u] =
    if a < u then 0 else rho8Value a b c u + 1 := by
  simp only [checkRho8,modelChooseLess,modelProjection,PRAMultiplication.modelZero,modelUnary,modelSucc,rho8_model,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

theorem rho8_accepts_iff (a b c u : M) :
    F checkRho8 ![a,b,c,u] = rho8Value a b c u + 1 ↔ u ≤ a := by
  rw [checkRho8_model]
  by_cases h : a < u
  · simp [h,not_le_of_gt h,zero_ne_add_one]
  · simp [h,le_of_not_gt h]

#print axioms checkRho8_model
#print axioms rho8_accepts_iff
end models
end PA194TargetRho8
