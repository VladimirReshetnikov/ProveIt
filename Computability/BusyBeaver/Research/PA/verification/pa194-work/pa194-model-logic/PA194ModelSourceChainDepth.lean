import PA194ModelSyntacticDescendant

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

/-- Sum of binder bits scanning a node stack backwards from a fixed endpoint. -/
noncomputable def chainDepthStep : Code 4 :=
  bin addCode (.proj 1)
    (unary binderBit
      (bin PA194TargetStep.lookup
        (bin subCode (.proj 2) (unary .succ (.proj 0))) (.proj 3)))
noncomputable def chainDepth : Code 3 := .prec (.zero 2) chainDepthStep

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

theorem chainDepth_zero (length nodes : M) : F chainDepth ![0,length,nodes] = 0 := by
  have h := PRAAddOne.modelBase (M := M) (.zero 2) chainDepthStep ![length,nodes]
  change F chainDepth ![0,length,nodes] = F (.zero 2) ![length,nodes] at h
  rw [PRAMultiplication.modelZero] at h
  exact h

theorem chainDepth_succ (k length nodes : M) :
    F chainDepth ![k+1,length,nodes] = F chainDepth ![k,length,nodes] +
      F binderBit ![F PA194TargetStep.lookup ![F subCode ![length,k+1],nodes]] := by
  have h := PRAAddOne.modelStep (M := M) (.zero 2) chainDepthStep ![k,length,nodes]
  change F chainDepth ![F Code.succ (fun _ => k),length,nodes] =
    F chainDepthStep ![k,F chainDepth ![k,length,nodes],length,nodes] at h
  change F chainDepth ![F addCode ![k,F oneCode Fin.elim0],length,nodes] = _
  rw [modelAddOne,h]
  simp only [chainDepthStep,modelBin,modelProjection,modelUnary,modelSucc,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  congr 3
  congr 1
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

theorem exactChainInvariant_definable (R : M → M → M → Prop) (start stage : M → M)
    (target length : M) (hr : 𝚺₁-Relation₃ R) (hs : 𝚺₁-Function₁ start)
    (hd : 𝚺₁-Function₁ stage) :
    𝚺₁-Predicate (fun k : M => k ≤ length → R (start k) target (stage k)) := by
  haveI := hr
  haveI := hs
  haveI := hd
  definability

theorem sourceChain_exact_depth (nodes length : M) (hchain : SourceChain nodes length) :
    ∀ k ≤ length, PathWithDepth
      (F PA194TargetStep.lookup ![F subCode ![length,k],nodes])
      (F PA194TargetStep.lookup ![length,nodes]) (F chainDepth ![k,length,nodes]) := by
  let start : M → M := fun k => F sourceChainStart ![k,length,nodes]
  let stage : M → M := fun k => F chainDepth ![k,length,nodes]
  let target := F PA194TargetStep.lookup ![length,nodes]
  have hr : 𝚺₁-Relation₃ (PathWithDepth (M := M)) := pathWithDepth_uniform_definable
  have hs : 𝚺₁-Function₁ start := PA194CodeInstance.unary_of_three sourceChainStart length nodes
  have hd : 𝚺₁-Function₁ stage := PA194CodeInstance.unary_of_three chainDepth length nodes
  have hdef := exactChainInvariant_definable (PathWithDepth (M := M)) start stage target length hr hs hd
  have hall : ∀ k : M, k ≤ length → PathWithDepth (start k) target (stage k) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _
      have hsub : F subCode ![length,0] = length := by
        have h := modelSubAdd (M := M) 0 length
        change F subCode ![(0 : M)+length,0] = length at h
        simpa only [zero_add] using h
      change PathWithDepth (F sourceChainStart ![0,length,nodes]) target (F chainDepth ![0,length,nodes])
      rw [sourceChainStart_model,hsub,chainDepth_zero]
      exact pathWithDepth_self target
    case succ k ih =>
      intro hk
      have hk' : k ≤ length := le_trans (le_of_lt (lt_add_one k)) hk
      obtain ⟨d,hd⟩ := le_iff_exists_add.mp hk
      have hsub1 : F subCode ![length,k+1] = d := by
        rw [hd]; exact modelSubAdd (k+1) d
      have hsub0 : F subCode ![length,k] = d+1 := by
        rw [hd]
        have he : (k+1)+d = k+(d+1) := by ac_rfl
        rw [he]; exact modelSubAdd k (d+1)
      have hj : d < length := by
        rw [hd]
        have hle : d+1 ≤ (k+1)+d := by
          have he : (k+1)+d = (d+1)+k := by ac_rfl
          rw [he]
          exact le_self_add
        exact lt_of_lt_of_le (lt_add_one d) hle
      obtain ⟨bit,hedge⟩ := hchain d hj
      have hpath := ih hk'
      change PathWithDepth (F sourceChainStart ![k,length,nodes]) target (F chainDepth ![k,length,nodes]) at hpath
      rw [sourceChainStart_model,hsub0] at hpath
      have hext := directEdge_extend_path _ _ _ bit (F chainDepth ![k,length,nodes]) hedge hpath
      obtain ⟨choice,hchoice,hbit⟩ := directEdge_choice _ _ bit hedge
      change PathWithDepth (F sourceChainStart ![k+1,length,nodes]) target (F chainDepth ![k+1,length,nodes])
      rw [sourceChainStart_model,hsub1,chainDepth_succ,hsub1,hbit]
      simpa only [add_comm] using hext
  intro k hk
  have h := hall k hk
  change PathWithDepth (F sourceChainStart ![k,length,nodes]) target (F chainDepth ![k,length,nodes]) at h
  rwa [sourceChainStart_model] at h

theorem sourceChain_root_exact_depth (nodes length : M) (hchain : SourceChain nodes length) :
    PathWithDepth (F PA194TargetStep.lookup ![0,nodes])
      (F PA194TargetStep.lookup ![length,nodes]) (F chainDepth ![length,length,nodes]) := by
  have h := sourceChain_exact_depth nodes length hchain length (le_refl length)
  have hsub : F subCode ![length,length] = 0 := by
    have hz := modelSubAdd length (0 : M)
    change F subCode ![length+0,length] = 0 at hz
    simpa only [add_zero] using hz
  rwa [hsub] at h

/-- Independent raw-syntax descendant with an explicit model-coded edge-bit sum. -/
def CodedDescendantAtDepth (root target depth : M) : Prop :=
  ∃ nodes length : M, SourceChain nodes length ∧
    F PA194TargetStep.lookup ![0,nodes] = root ∧
    F PA194TargetStep.lookup ![length,nodes] = target ∧
    F chainDepth ![length,length,nodes] = depth

theorem codedDescendantAtDepth_coverage (root target depth : M)
    (h : CodedDescendantAtDepth root target depth) : PathWithDepth root target depth := by
  obtain ⟨nodes,length,hchain,hroot,htarget,hdepth⟩ := h
  have hp := sourceChain_root_exact_depth nodes length hchain
  rwa [hroot,htarget,hdepth] at hp

#print axioms sourceChain_root_exact_depth
#print axioms codedDescendantAtDepth_coverage
#print axioms sourceChain_exact_depth
#print axioms chainDepth_zero
#print axioms chainDepth_succ
end models
end PA194ModelLogic
