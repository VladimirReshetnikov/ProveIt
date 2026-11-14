import PA194ModelPathPrepend

/-! Binder-count behavior when prefixing a source-path choice. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

noncomputable def shiftedBinderCount : Code 3 :=
  PA194TargetStep.app3 binderCount (unary .succ (.proj 0)) (.proj 1) (.proj 2)

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

theorem shiftedBinderCount_model (j root stack : M) :
    F shiftedBinderCount ![j,root,stack] = F binderCount ![j+1,root,stack] := by
  simp only [shiftedBinderCount,PA194TargetStep.app3_model,modelUnary,modelProjection,modelSucc,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_def,Matrix.cons_val_succ]

theorem binderCount_prepend (root choice rest i : M) :
    F binderCount ![i+1,root,pair choice rest+1] = F binderBit ![root] +
      F binderCount ![i,F sourceChild ![root,choice],rest] := by
  let child := F sourceChild ![root,choice]
  let stack := pair choice rest+1
  haveI : 𝚺₁-Function₁ (fun j : M => F shiftedBinderCount ![j,root,stack]) :=
    PA194CodeInstance.unary_of_three shiftedBinderCount root stack
  haveI : 𝚺₁-Function₁ (fun j : M => F binderCount ![j,child,rest]) :=
    PA194CodeInstance.unary_of_three binderCount child rest
  have hdef' : 𝚺₁-Predicate (fun j : M =>
      F shiftedBinderCount ![j,root,stack] = F binderBit ![root] +
        F binderCount ![j,child,rest]) := by definability
  have hdef : 𝚺₁-Predicate (fun j : M =>
      F binderCount ![j+1,root,stack] = F binderBit ![root] +
        F binderCount ![j,child,rest]) := by
    simpa only [shiftedBinderCount_model] using hdef'
  change F binderCount ![i+1,root,stack] = F binderBit ![root] + F binderCount ![i,child,rest]
  induction i using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => rw [binderCount_succ,binderCount_zero,binderCount_zero,sourcePath_zero,zero_add,add_zero]
  case succ i ih =>
    rw [binderCount_succ (i+1),binderCount_succ i child rest,ih]
    change (F binderBit ![root] + F binderCount ![i,child,rest]) +
      F binderBit ![F sourcePath ![i+1,root,pair choice rest+1]] = _
    rw [sourcePath_prepend]
    ac_rfl

#print axioms binderCount_prepend
end models
end PA194ModelLogic
