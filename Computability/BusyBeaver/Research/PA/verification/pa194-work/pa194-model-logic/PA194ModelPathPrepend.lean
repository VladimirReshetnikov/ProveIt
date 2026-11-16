import PA194ModelPathDispatcherFresh

/-! Prefixing a choice to a model-length source path. -/
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

noncomputable def shiftedSourcePath : Code 3 :=
  PA194TargetStep.app3 sourcePath (unary .succ (.proj 0)) (.proj 1) (.proj 2)

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

theorem shiftedSourcePath_model (j root stack : M) :
    F shiftedSourcePath ![j,root,stack] = F sourcePath ![j+1,root,stack] := by
  simp only [shiftedSourcePath,PA194TargetStep.app3_model,modelUnary,modelProjection,modelSucc,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,Matrix.cons_val_succ]

/-- Prefixing a choice follows one edge, then continues with the old choice
stack. Holds for arbitrary model-length paths, including nonstandard ones. -/
theorem sourcePath_prepend (root choice rest i : M) :
    F sourcePath ![i+1,root,pair choice rest+1] =
      F sourcePath ![i,F sourceChild ![root,choice],rest] := by
  let child := F sourceChild ![root,choice]
  let stack := pair choice rest+1
  haveI : 𝚺₁-Function₁ (fun j : M => F sourcePath ![j,root,stack]) :=
    PA194CodeInstance.unary_of_three sourcePath root stack
  haveI : 𝚺₁-Function₁ (fun j : M => F sourcePath ![j,child,rest]) :=
    PA194CodeInstance.unary_of_three sourcePath child rest
  haveI : 𝚺₁-Function₁ (fun j : M => F shiftedSourcePath ![j,root,stack]) :=
    PA194CodeInstance.unary_of_three shiftedSourcePath root stack
  have hdef' : 𝚺₁-Predicate (fun j : M =>
      F shiftedSourcePath ![j,root,stack] = F sourcePath ![j,child,rest]) := by definability
  have hdef : 𝚺₁-Predicate (fun j : M =>
      F sourcePath ![j+1,root,stack] = F sourcePath ![j,child,rest]) := by
    simpa only [shiftedSourcePath_model] using hdef' 
  change F sourcePath ![i+1,root,stack] = F sourcePath ![i,child,rest]
  induction i using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero =>
    rw [sourcePath_succ,sourcePath_zero,sourcePath_zero]
    change F sourceChild ![root,F PA194TargetStep.lookup ![0,pair choice rest+1]] = child
    have hz := modelLookupZero firstProjection secondProjection firstProjection_certified choice rest
    change F PA194TargetStep.lookup ![0,pair choice rest+1] = choice at hz
    rw [hz]
  case succ i ih =>
    rw [sourcePath_succ (i+1), sourcePath_succ i child rest, ih]
    change F sourceChild ![F sourcePath ![i,child,rest],
      F PA194TargetStep.lookup ![i+1,pair choice rest+1]] = _
    have hs := modelLookupConsSucc firstProjection secondProjection secondProjection_certified i choice rest
    change F PA194TargetStep.lookup ![i+1,pair choice rest+1] =
      F PA194TargetStep.lookup ![i,rest] at hs
    rw [hs]

#print axioms sourcePath_prepend
end models
end PA194ModelLogic
