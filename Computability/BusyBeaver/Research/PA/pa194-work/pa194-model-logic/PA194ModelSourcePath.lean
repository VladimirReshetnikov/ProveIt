import PA194ModelAtomicFreshness

/-! A finite PRA code for model-length source-syntax paths. Binary nodes follow
a supplied choice, quantifiers descend to their body, and the four leaf tags
are stationary. The code does not by itself validate the source formula. -/
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
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

noncomputable def pathTag : Code 2 := unary firstProjection (unary predCode (.proj 0))
noncomputable def pathPayload : Code 2 := unary secondProjection (unary predCode (.proj 0))
noncomputable def pathLeft : Code 2 := unary firstProjection pathPayload
noncomputable def pathRight : Code 2 := unary secondProjection pathPayload
noncomputable def pathBinary : Code 2 := selectAmong (.proj 1) pathLeft pathRight
/-- Input source node and a choice: nonzero chooses the left Boolean child. -/
noncomputable def sourceChild : Code 2 :=
  let test (n : Nat) := bin equalityCode pathTag (numeralCode 2 n)
  selectAmong (test 4) pathBinary
    (selectAmong (test 5) pathBinary
      (selectAmong (test 6) pathPayload (selectAmong (test 7) pathPayload (.proj 0))))
/-- Primitive recursion inputs are step index, preceding node, root and choice stack. -/
noncomputable def sourcePathStep : Code 4 :=
  bin sourceChild (.proj 1) (bin PA194TargetStep.lookup (.proj 0) (.proj 3))
/-- Inputs: model step count, root code, pair-plus-one choice stack. -/
noncomputable def sourcePath : Code 3 := .prec (.proj 0) sourcePathStep

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

theorem pathComponents_model (t payload choice : M) :
    let e := ![pair t payload+1,choice]
    F pathTag e = t ∧ F pathPayload e = payload ∧
      F pathLeft e = π₁ payload ∧ F pathRight e = π₂ payload := by
  simp only [pathTag,pathPayload,pathLeft,pathRight,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    modelPredAddOne,pi₁_pair,pi₂_pair]
  simp

/-- For either Boolean tag, a nonzero choice selects the left child and zero the right. -/
theorem sourceChild_binary (tag p q choice : M) (ht : tag = 4 ∨ tag = 5) :
    F sourceChild ![pair tag (pair p q)+1,choice] = F selectCode ![choice,p,q] := by
  have hc := pathComponents_model tag (pair p q) choice
  dsimp only at hc
  unfold sourceChild
  simp only [modelChooseEqual,modelNumeralCode,hc.1]
  rcases ht with rfl | rfl <;> norm_num
  all_goals
    rw [pathBinary,modelSelectAmong,modelProjection,hc.2.2.1,hc.2.2.2,pi₁_pair,pi₂_pair]
    rfl

/-- A quantifier tag selects its body. -/
theorem sourceChild_binder (tag p choice : M) (ht : tag = 6 ∨ tag = 7) :
    F sourceChild ![pair tag p+1,choice] = p := by
  have hc := pathComponents_model tag p choice
  dsimp only at hc
  unfold sourceChild
  simp only [modelChooseEqual,modelNumeralCode,hc.1]
  rcases ht with rfl | rfl <;> norm_num
  all_goals exact hc.2.1

/-- The positive/negative atom and truth/falsity tags are stationary. -/
theorem sourceChild_leaf (tag payload choice : M)
    (ht : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3) :
    F sourceChild ![pair tag payload+1,choice] = pair tag payload+1 := by
  have hc := pathComponents_model tag payload choice
  dsimp only at hc
  unfold sourceChild
  simp only [modelChooseEqual,modelNumeralCode,hc.1]
  rcases ht with rfl | rfl | rfl | rfl <;> norm_num
  all_goals rw [modelProjection]
  all_goals rfl

#print axioms sourceChild_binary
#print axioms sourceChild_binder
#print axioms sourceChild_leaf

theorem select_bounded (test yes no ceiling : M) (hy : yes ≤ ceiling) (hn : no ≤ ceiling) :
    F selectCode ![test,yes,no] ≤ ceiling := by
  rcases zero_or_succ test with (rfl | ⟨j,rfl⟩)
  · have h := modelSelectZero (M := M) yes no
    change F selectCode ![(0 : M),yes,no] = no at h
    rw [h]; exact hn
  · have h := modelSelectSucc (M := M) j yes no
    change F selectCode ![F Code.succ (fun _ => j),yes,no] = yes at h
    rw [modelSucc] at h
    rw [h]; exact hy

theorem projection_le (v : M) : π₁ v ≤ v ∧ π₂ v ≤ v := by
  have h := pair_unpair v
  constructor
  · calc π₁ v ≤ pair (π₁ v) (π₂ v) := le_pair_left _ _
      _ = v := h
  · calc π₂ v ≤ pair (π₁ v) (π₂ v) := le_pair_right _ _
      _ = v := h

theorem predecessor_le (v : M) : F predCode (fun _ => v) ≤ v := by
  rcases zero_or_succ v with (rfl | ⟨j,rfl⟩)
  · have h := PRASubReconstruct.modelPredZero (M := M)
    change F predCode (fun _ => (0 : M)) = 0 at h
    rw [h]
  · rw [modelPredAddOne]; exact le_of_lt (lt_add_one _)

theorem sourceChild_le (p choice : M) : F sourceChild ![p,choice] ≤ p := by
  let d := F predCode (fun _ => p)
  have hd : d ≤ p := predecessor_le p
  have ht : π₂ d ≤ p := le_trans (projection_le d).2 hd
  have hl : π₁ (π₂ d) ≤ p := le_trans (projection_le (π₂ d)).1 ht
  have hr : π₂ (π₂ d) ≤ p := le_trans (projection_le (π₂ d)).2 ht
  have hbin : F pathBinary ![p,choice] ≤ p := by
    simp only [pathBinary,modelSelectAmong,pathLeft,pathRight,pathPayload,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,
      modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,Matrix.cons_val_one]
    change F selectCode ![choice,π₁ (π₂ d),π₂ (π₂ d)] ≤ p
    exact select_bounded choice _ _ p hl hr
  have htail : F pathPayload ![p,choice] ≤ p := by
    rw [pathPayload,modelUnary,modelUnary,modelProjection,
      modelPi2Code secondProjection secondProjection_certified]
    exact ht
  unfold sourceChild
  repeat' rw [modelSelectAmong]
  apply select_bounded
  · exact hbin
  apply select_bounded
  · exact hbin
  apply select_bounded
  · exact htail
  apply select_bounded
  · exact htail
  · rw [modelProjection]; rfl

theorem sourcePath_zero (root choices : M) : F sourcePath ![0,root,choices] = root := by
  have h := PRAAddOne.modelBase (M := M) (.proj 0 : Code 2) sourcePathStep ![root,choices]
  change F sourcePath ![0,root,choices] = F (.proj 0 : Code 2) ![root,choices] at h
  rw [modelProjection] at h
  exact h

theorem sourcePath_succ (i root choices : M) :
    F sourcePath ![i+1,root,choices] =
      F sourceChild ![F sourcePath ![i,root,choices],F PA194TargetStep.lookup ![i,choices]] := by
  have h := PRAAddOne.modelStep (M := M) (.proj 0 : Code 2) sourcePathStep ![i,root,choices]
  change F sourcePath ![F Code.succ (fun _ => i),root,choices] =
    F sourcePathStep ![i,F sourcePath ![i,root,choices],root,choices] at h
  change F sourcePath ![F addCode ![i,F oneCode Fin.elim0],root,choices] = _
  rw [modelAddOne,h,sourcePathStep,modelBin,modelBin,modelProjection,modelProjection,modelProjection]
  rfl

theorem sourcePath_le_root (root choices i : M) : F sourcePath ![i,root,choices] ≤ root := by
  haveI : 𝚺₁-Function₁ (fun i : M => F sourcePath ![i,root,choices]) :=
    PA194CodeInstance.unary_of_three sourcePath root choices
  have hdef : 𝚺₁-Predicate (fun i : M => F sourcePath ![i,root,choices] ≤ root) := by definability
  induction i using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => rw [sourcePath_zero]
  case succ i ih =>
    rw [sourcePath_succ]
    exact le_trans (sourceChild_le _ _) ih

/-- Every source-variable index at a reached valid atomic node is below the root,
even when the path length is nonstandard. -/
theorem sourcePath_atomIndices_lt_root (root choices steps tag relation v : M)
    (hnode : F sourcePath ![steps,root,choices] = pair tag (pair 2 (pair relation v))+1)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      ∀ i : M, (a = ^#i ∨ a = ^&i ∨ b = ^#i ∨ b = ^&i) → i < root := by
  have hle := sourcePath_le_root root choices steps
  rw [hnode] at hle
  obtain ⟨a,b,ha,hb,hi⟩ := sourceAtom_termIndices_lt hv tag relation
  refine ⟨a,b,ha,hb,?_⟩
  intro i h
  exact lt_of_lt_of_le (hi i h) hle

/-- At any reached valid atomic node, the labels selected from any bounded
allocation stage and the fixed free stack are below the reserved label. -/
theorem sourcePath_atomLabels_fresh (root choices steps tag relation v n base initial free reserve : M)
    (hnode : F sourcePath ![steps,root,choices] = pair tag (pair 2 (pair relation v))+1)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v)
    (hn : n ≤ root) (hreserve : base+root ≤ reserve)
    (hinit : ∀ i ≤ root, initial.[i] < reserve)
    (hfree : ∀ i ≤ root, free.[i] < reserve) :
    let bound := F allocateBound ![n,base,initial]
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧ IsUTerm M6.PA.RelationalSource.language b ∧
      F termLabelCode ![a,bound,free] < reserve ∧ F termLabelCode ![b,bound,free] < reserve := by
  have hatom := sourcePath_le_root root choices steps
  rw [hnode] at hatom
  exact allocatedSourceAtom_labels_fresh hv tag relation n base initial free root reserve
    hatom hn hreserve hinit hfree

#print axioms sourcePath_atomIndices_lt_root
#print axioms sourcePath_atomLabels_fresh
#print axioms pathComponents_model
#print axioms select_bounded
#print axioms sourceChild_le
#print axioms sourcePath_zero
#print axioms sourcePath_succ
#print axioms sourcePath_le_root
end models
end PA194ModelLogic
