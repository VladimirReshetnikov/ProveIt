import PA194ModelDirectEdge

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

/-- A model-coded, independently specified sequence of immediate source edges.
The pair-plus-one stack stores nodes; it need not be well-formed syntax unless
that is imposed separately. -/
def SourceChain (nodes length : M) : Prop :=
  ∀ j < length, ∃ binder : M,
    SourceDirectEdge (F PA194TargetStep.lookup ![j,nodes])
      (F PA194TargetStep.lookup ![j+1,nodes]) binder

noncomputable def sourceChainStart : Code 3 :=
  bin PA194TargetStep.lookup (bin subCode (.proj 1) (.proj 0)) (.proj 2)

theorem sourceChainStart_model (k length nodes : M) :
    F sourceChainStart ![k,length,nodes] =
      F PA194TargetStep.lookup ![F subCode ![length,k],nodes] := by
  simp only [sourceChainStart,modelBin,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,Matrix.cons_val_succ]

theorem chainInvariant_definable (R : M → M → M → Prop) (start : M → M)
    (target length : M) (hr : 𝚺₁-Relation₃ R) (hs : 𝚺₁-Function₁ start) :
    𝚺₁-Predicate (fun k : M => k ≤ length → ∃ depth, R (start k) target depth) := by
  haveI := hr
  haveI := hs
  definability

theorem sourceChain_reachability (nodes length : M) (hchain : SourceChain nodes length) :
    ∀ k ≤ length, ∃ depth : M, PathWithDepth
      (F PA194TargetStep.lookup ![F subCode ![length,k],nodes])
      (F PA194TargetStep.lookup ![length,nodes]) depth := by
  let start : M → M := fun k => F sourceChainStart ![k,length,nodes]
  let target := F PA194TargetStep.lookup ![length,nodes]
  have hr : 𝚺₁-Relation₃ (PathWithDepth (M := M)) := pathWithDepth_uniform_definable
  have hs : 𝚺₁-Function₁ start := PA194CodeInstance.unary_of_three sourceChainStart length nodes
  have hdef := chainInvariant_definable (PathWithDepth (M := M)) start target length hr hs
  have hall : ∀ k : M, k ≤ length → ∃ depth, PathWithDepth (start k) target depth := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _
      have hsub : F subCode ![length,0] = length := by
        have h := modelSubAdd (M := M) 0 length
        change F subCode ![(0 : M)+length,0] = length at h
        simpa only [zero_add] using h
      refine ⟨0,?_⟩
      change PathWithDepth (F sourceChainStart ![0,length,nodes]) target 0
      rw [sourceChainStart_model,hsub]
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
      obtain ⟨depth,hpath⟩ := ih hk'
      change PathWithDepth (F sourceChainStart ![k,length,nodes]) target depth at hpath
      rw [sourceChainStart_model,hsub0] at hpath
      refine ⟨bit+depth,?_⟩
      change PathWithDepth (F sourceChainStart ![k+1,length,nodes]) target (bit+depth)
      rw [sourceChainStart_model,hsub1]
      exact directEdge_extend_path _ _ _ bit depth hedge hpath
  intro k hk
  obtain ⟨depth,h⟩ := hall k hk
  refine ⟨depth,?_⟩
  change PathWithDepth (F sourceChainStart ![k,length,nodes]) target depth at h
  rw [sourceChainStart_model] at h
  exact h

/-- Every independently coded source-edge chain has a coded path from its first
to its last node, for some model-valued binder depth. -/
theorem sourceChain_rootToTarget (nodes length : M) (hchain : SourceChain nodes length) :
    ∃ depth : M, PathWithDepth (F PA194TargetStep.lookup ![0,nodes])
      (F PA194TargetStep.lookup ![length,nodes]) depth := by
  have h := sourceChain_reachability nodes length hchain length (le_refl length)
  have hsub : F subCode ![length,length] = 0 := by
    have hz := modelSubAdd length (0 : M)
    change F subCode ![length+0,length] = 0 at hz
    simpa only [add_zero] using hz
  rw [hsub] at h
  exact h

/-- A source-edge chain starting at valid syntax ends at valid syntax. -/
theorem sourceChain_target_valid (nodes length : M) (hchain : SourceChain nodes length)
    (hroot : IsUFormula M6.PA.RelationalSource.language (F PA194TargetStep.lookup ![0,nodes])) :
    IsUFormula M6.PA.RelationalSource.language (F PA194TargetStep.lookup ![length,nodes]) := by
  obtain ⟨depth,i,choices,hpath,hcount⟩ := sourceChain_rootToTarget nodes length hchain
  rw [← hpath]
  exact sourcePath_preserves_formula _ choices i hroot

#print axioms sourceChain_rootToTarget
#print axioms sourceChain_target_valid
#print axioms sourceChain_reachability
end models
end PA194ModelLogic
