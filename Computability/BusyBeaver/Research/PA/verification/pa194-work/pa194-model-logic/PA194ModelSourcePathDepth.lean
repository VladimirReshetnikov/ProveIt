import PA194ModelSourcePath

/-! Model-length count of binders encountered by the source path. The counter
uses the same sourcePath and choice stack; no coverage/completeness of paths
for all internal subformulas is claimed. -/
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

noncomputable def nodeTag : Code 1 := unary firstProjection (unary predCode (.proj 0))
noncomputable def binderBit : Code 1 :=
  selectAmong (bin equalityCode nodeTag (numeralCode 1 6)) (numeralCode 1 1)
    (selectAmong (bin equalityCode nodeTag (numeralCode 1 7)) (numeralCode 1 1) (.zero 1))
/-- Recursion receives step, prior count, root and choice stack. -/
noncomputable def binderCountStep : Code 4 :=
  bin addCode (.proj 1) (unary binderBit (PA194TargetStep.app3 sourcePath (.proj 0) (.proj 2) (.proj 3)))
/-- Inputs: model step count, root source code and choice stack. -/
noncomputable def binderCount : Code 3 := .prec (.zero 2) binderCountStep

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

theorem nodeTag_model (tag payload : M) : F nodeTag ![pair tag payload+1] = tag := by
  simp only [nodeTag,modelUnary,modelProjection,modelPi1Code firstProjection firstProjection_certified,
    Matrix.cons_val_zero,modelPredAddOne,pi₁_pair]

theorem binderBit_model (p : M) :
    F binderBit ![p] = if F nodeTag ![p] = 6 then 1 else if F nodeTag ![p] = 7 then 1 else 0 := by
  simp only [binderBit,modelChooseEqual,modelNumeralCode,PRAMultiplication.modelZero]
  norm_num
  rfl

theorem binderBit_le_one (p : M) : F binderBit ![p] ≤ 1 := by
  rw [binderBit_model]
  split_ifs <;> simp

theorem binderCount_zero (root choices : M) : F binderCount ![0,root,choices] = 0 := by
  have h := PRAAddOne.modelBase (M := M) (.zero 2) binderCountStep ![root,choices]
  change F binderCount ![0,root,choices] = F (.zero 2) ![root,choices] at h
  rw [PRAMultiplication.modelZero] at h
  exact h

theorem binderCount_succ (i root choices : M) :
    F binderCount ![i+1,root,choices] =
      F binderCount ![i,root,choices] + F binderBit ![F sourcePath ![i,root,choices]] := by
  have h := PRAAddOne.modelStep (M := M) (.zero 2) binderCountStep ![i,root,choices]
  change F binderCount ![F Code.succ (fun _ => i),root,choices] =
    F binderCountStep ![i,F binderCount ![i,root,choices],root,choices] at h
  change F binderCount ![F addCode ![i,F oneCode Fin.elim0],root,choices] = _
  rw [modelAddOne,h,binderCountStep,modelBin,modelProjection,modelUnary,PA194TargetStep.app3_model]
  simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  congr 3
  congr 1
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

theorem binderCount_le_steps (root choices steps : M) : F binderCount ![steps,root,choices] ≤ steps := by
  haveI : 𝚺₁-Function₁ (fun i : M => F binderCount ![i,root,choices]) :=
    PA194CodeInstance.unary_of_three binderCount root choices
  have hdef : 𝚺₁-Predicate (fun i : M => F binderCount ![i,root,choices] ≤ i) := by definability
  induction steps using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => rw [binderCount_zero]
  case succ i ih =>
    rw [binderCount_succ]
    exact add_le_add ih (binderBit_le_one _)

theorem sourceChild_progress (p choice : M) :
    F sourceChild ![p,choice] + F binderBit ![p] ≤ p := by
  rcases zero_or_succ p with (rfl | ⟨d,rfl⟩)
  · have ht : F nodeTag ![(0 : M)] = 0 := by
      rw [nodeTag, modelUnary, modelUnary, modelProjection,
        modelPi1Code firstProjection firstProjection_certified]
      change π₁ (F predCode (fun _ => (0 : M))) = 0
      have hz := PRASubReconstruct.modelPredZero (M := M)
      change F predCode (fun _ => (0 : M)) = 0 at hz
      rw [hz]
      exact le_antisymm (projection_le 0).1 zero_le
    rw [binderBit_model,ht]
    norm_num
    exact le_antisymm (sourceChild_le 0 choice) zero_le
  · nth_rewrite 1 2 3 [← pair_unpair d]
    rw [binderBit_model,nodeTag_model]
    by_cases h6 : π₁ d = 6
    · rw [if_pos h6]
      rw [sourceChild_binder _ _ _ (Or.inl h6)]
      simpa only [add_comm] using (add_le_add_right (le_pair_right (π₁ d) (π₂ d)) (1 : M))
    · by_cases h7 : π₁ d = 7
      · rw [if_neg h6, if_pos h7]
        rw [sourceChild_binder _ _ _ (Or.inr h7)]
        simpa only [add_comm] using (add_le_add_right (le_pair_right (π₁ d) (π₂ d)) (1 : M))
      · rw [if_neg h6, if_neg h7, add_zero]
        exact sourceChild_le _ _

/-- Every counted binder consumes at least one unit of source-code size,
including for nonstandard step counts and paths that stall at a leaf. -/
theorem sourcePath_count_budget (root choices steps : M) :
    F sourcePath ![steps,root,choices] + F binderCount ![steps,root,choices] ≤ root := by
  haveI : 𝚺₁-Function₁ (fun i : M => F sourcePath ![i,root,choices]) :=
    PA194CodeInstance.unary_of_three sourcePath root choices
  haveI : 𝚺₁-Function₁ (fun i : M => F binderCount ![i,root,choices]) :=
    PA194CodeInstance.unary_of_three binderCount root choices
  have hdef : 𝚺₁-Predicate (fun i : M =>
      F sourcePath ![i,root,choices] + F binderCount ![i,root,choices] ≤ root) := by definability
  induction steps using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => rw [sourcePath_zero,binderCount_zero,add_zero]
  case succ i ih =>
    rw [sourcePath_succ,binderCount_succ]
    have hs := sourceChild_progress (F sourcePath ![i,root,choices])
      (F PA194TargetStep.lookup ![i,choices])
    calc
      F sourceChild ![F sourcePath ![i,root,choices], F PA194TargetStep.lookup ![i,choices]] +
          (F binderCount ![i,root,choices] + F binderBit ![F sourcePath ![i,root,choices]]) =
          F binderCount ![i,root,choices] +
            (F sourceChild ![F sourcePath ![i,root,choices], F PA194TargetStep.lookup ![i,choices]] +
              F binderBit ![F sourcePath ![i,root,choices]]) := by ac_rfl
      _ ≤ F binderCount ![i,root,choices] + F sourcePath ![i,root,choices] := by
        exact add_le_add_right hs _
      _ ≤ root := by simpa only [add_comm] using ih

theorem binderCount_le_root (root choices steps : M) : F binderCount ![steps,root,choices] ≤ root := by
  have h : F binderCount ![steps,root,choices] ≤
      F sourcePath ![steps,root,choices] + F binderCount ![steps,root,choices] := by
    simpa only [add_comm] using (le_self_add : F binderCount ![steps,root,choices] ≤
      F binderCount ![steps,root,choices] + F sourcePath ![steps,root,choices])
  exact le_trans h (sourcePath_count_budget root choices steps)

/-- Freshness at reached well-formed atoms using precisely the traversed binder count. -/
theorem sourcePath_atomLabels_fresh_count (root choices steps tag relation v base initial free reserve : M)
    (hnode : F sourcePath ![steps,root,choices] = pair tag (pair 2 (pair relation v))+1)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v)
    (hreserve : base+root ≤ reserve)
    (hinit : ∀ i ≤ root, initial.[i] < reserve)
    (hfree : ∀ i ≤ root, free.[i] < reserve) :
    let bound := F allocateBound ![F binderCount ![steps,root,choices],base,initial]
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      F termLabelCode ![a,bound,free] < reserve ∧ F termLabelCode ![b,bound,free] < reserve := by
  exact sourcePath_atomLabels_fresh root choices steps tag relation v _ base initial free reserve
    hnode hv (binderCount_le_root root choices steps) hreserve hinit hfree

#print axioms sourcePath_atomLabels_fresh_count
#print axioms sourceChild_progress
#print axioms sourcePath_count_budget
#print axioms binderCount_le_root
#print axioms nodeTag_model
#print axioms binderBit_model
#print axioms binderBit_le_one
#print axioms binderCount_zero
#print axioms binderCount_succ
#print axioms binderCount_le_steps
end models
end PA194ModelLogic
