import PA194ModelPathReachability

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

noncomputable def pathDepthResult : Code 3 := bin pairCode sourcePath binderCount
noncomputable def packedPathDepthWitness : Code 3 :=
  PA194TargetStep.app3 pathDepthResult (unary firstProjection (.proj 0)) (.proj 1)
    (unary secondProjection (.proj 0))
noncomputable def packedPathDepthWitness4 : Code 4 :=
  PA194TargetStep.app3 packedPathDepthWitness (.proj 0) (.proj 1) (.zero 4)

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

theorem packedPathDepthWitness_model (w root dummy : M) :
    F packedPathDepthWitness ![w,root,dummy] =
      pair (F sourcePath ![π₁ w,root,π₂ w]) (F binderCount ![π₁ w,root,π₂ w]) := by
  simp only [packedPathDepthWitness,PA194TargetStep.app3_model,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_def,Matrix.cons_val_succ,pathDepthResult,modelBin,modelPairCode]

theorem pathWithDepth_iff_packed (root target depth : M) :
    PathWithDepth root target depth ↔
      ∃ w : M, F packedPathDepthWitness ![w,root,0] = pair target depth := by
  constructor
  · rintro ⟨i,choices,hp,hc⟩
    refine ⟨pair i choices,?_⟩
    rw [packedPathDepthWitness_model,pi₁_pair,pi₂_pair,hp,hc]
  · rintro ⟨w,hw⟩
    rw [packedPathDepthWitness_model] at hw
    have hp := congrArg (fun x : M => π₁ x) hw
    have hc := congrArg (fun x : M => π₂ x) hw
    rw [pi₁_pair,pi₁_pair] at hp
    rw [pi₂_pair,pi₂_pair] at hc
    exact ⟨π₁ w,π₂ w,hp,hc⟩

theorem pairImage_definable (f : M → M) (hf : 𝚺₁-Function₁ f) :
    𝚺₁-Relation (fun target depth : M => ∃ w : M, f w = pair target depth) := by
  haveI := hf
  definability

theorem pathWithDepth_definable (root : M) :
    𝚺₁-Relation (fun target depth : M => PathWithDepth root target depth) := by
  let f : M → M := fun w => F packedPathDepthWitness ![w,root,0]
  haveI : 𝚺₁-Function₁ f := PA194CodeInstance.unary_of_three packedPathDepthWitness root 0
  have hp := pairImage_definable f (PA194CodeInstance.unary_of_three packedPathDepthWitness root 0)
  change 𝚺₁-Relation (fun target depth : M => ∃ w : M,
    F packedPathDepthWitness ![w,root,0] = pair target depth) at hp
  simpa only [← pathWithDepth_iff_packed] using hp

theorem packedPathDepthWitness4_model (w root a b : M) :
    F packedPathDepthWitness4 ![w,root,a,b] = F packedPathDepthWitness ![w,root,0] := by
  simp only [packedPathDepthWitness4,PA194TargetStep.app3_model,modelProjection,
    PRAMultiplication.modelZero,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rfl

theorem pairImage3_definable (f : M → M → M) (hf : 𝚺₁-Function₂ f) :
    𝚺₁.Definable (fun v : Fin 3 → M => ∃ w : M, f w (v 0) = pair (v 1) (v 2)) := by
  haveI := hf
  definability

theorem pathWithDepth_uniform_definable :
    𝚺₁.Definable (fun v : Fin 3 → M => PathWithDepth (v 0) (v 1) (v 2)) := by
  let f : M → M → M := fun w root => F packedPathDepthWitness ![w,root,0]
  have hf : 𝚺₁-Function₂ f := by
    have h := evalTwo_definable (M := M) packedPathDepthWitness4 (0 : M) (0 : M)
    simpa only [packedPathDepthWitness4_model] using h
  have hp := pairImage3_definable f hf
  change 𝚺₁.Definable (fun v : Fin 3 → M => ∃ w : M,
    F packedPathDepthWitness ![w,v 0,0] = pair (v 1) (v 2)) at hp
  simpa only [← pathWithDepth_iff_packed] using hp

#print axioms pathWithDepth_uniform_definable
#print axioms pathWithDepth_iff_packed
#print axioms pathWithDepth_definable
#print axioms packedPathDepthWitness_model
end models
end PA194ModelLogic
