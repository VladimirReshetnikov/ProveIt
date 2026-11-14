import PA194ModelRecursorOccurrence

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

/-- Explicit one-step reference-recursion occurrence relation: valid constructor
child and the budget change established by the reference constructor equations. -/
def FormulaReferenceEdge (parent parentBudget child childBudget : M) : Prop :=
  IsUFormula M6.PA.RelationalSource.language parent ∧
  IsUFormula M6.PA.RelationalSource.language child ∧
  ∃ bit : M, SourceDirectEdge parent child bit ∧ parentBudget = childBudget+bit

theorem formulaReferenceEdge_and (p q b : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    FormulaReferenceEdge (pair (4 : M) (pair p q)+1) b p b ∧
      FormulaReferenceEdge (pair (4 : M) (pair p q)+1) b q b := by
  have hv : IsUFormula M6.PA.RelationalSource.language (pair (4 : M) (pair p q)+1) := by
    simpa only [qqAnd] using (IsUFormula.and.mpr ⟨hp,hq⟩)
  refine ⟨⟨hv,hp,0,Or.inl ⟨p,q,rfl,Or.inl rfl,rfl⟩,?_⟩,
    ⟨hv,hq,0,Or.inl ⟨p,q,rfl,Or.inr rfl,rfl⟩,?_⟩⟩ <;> simp

theorem formulaReferenceEdge_or (p q b : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    FormulaReferenceEdge (pair (5 : M) (pair p q)+1) b p b ∧
      FormulaReferenceEdge (pair (5 : M) (pair p q)+1) b q b := by
  have hv : IsUFormula M6.PA.RelationalSource.language (pair (5 : M) (pair p q)+1) := by
    simpa only [qqOr] using (IsUFormula.or.mpr ⟨hp,hq⟩)
  refine ⟨⟨hv,hp,0,Or.inr (Or.inl ⟨p,q,rfl,Or.inl rfl,rfl⟩),?_⟩,
    ⟨hv,hq,0,Or.inr (Or.inl ⟨p,q,rfl,Or.inr rfl,rfl⟩),?_⟩⟩ <;> simp

theorem formulaReferenceEdge_all (p b : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    FormulaReferenceEdge (pair (6 : M) p+1) (b+1) p b := by
  have hv : IsUFormula M6.PA.RelationalSource.language (pair (6 : M) p+1) := by
    simpa only [qqAll] using (IsUFormula.all.mpr hp)
  exact ⟨hv,hp,1,Or.inr (Or.inr (Or.inl ⟨p,rfl,rfl,rfl⟩)),rfl⟩

theorem formulaReferenceEdge_ex (p b : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    FormulaReferenceEdge (pair (7 : M) p+1) (b+1) p b := by
  have hv : IsUFormula M6.PA.RelationalSource.language (pair (7 : M) p+1) := by
    simpa only [qqExs] using (IsUFormula.ex.mpr hp)
  exact ⟨hv,hp,1,Or.inr (Or.inr (Or.inr ⟨p,rfl,rfl,rfl⟩)),rfl⟩

/-- An explicit model-coded sequence of those local recursion occurrences; this
is not asserted to encode every Foundation fixpoint/history witness. -/
def FormulaReferenceChain (nodes budgets length : M) : Prop :=
  ∀ j < length, FormulaReferenceEdge
    (F PA194TargetStep.lookup ![j,nodes]) (F PA194TargetStep.lookup ![j,budgets])
    (F PA194TargetStep.lookup ![j+1,nodes]) (F PA194TargetStep.lookup ![j+1,budgets])

theorem formulaReferenceChain_sourceChain (nodes budgets length : M)
    (h : FormulaReferenceChain nodes budgets length) : SourceChain nodes length := by
  intro j hj
  obtain ⟨_,_,bit,he,_⟩ := h j hj
  exact ⟨bit,he⟩

theorem formulaReferenceChain_coverage (nodes budgets length : M)
    (h : FormulaReferenceChain nodes budgets length) :
    PathWithDepth (F PA194TargetStep.lookup ![0,nodes])
      (F PA194TargetStep.lookup ![length,nodes]) (F chainDepth ![length,length,nodes]) := by
  exact sourceChain_root_exact_depth nodes length (formulaReferenceChain_sourceChain nodes budgets length h)

theorem budgetInvariant_definable (start stage : M → M) (target length : M)
    (hs : 𝚺₁-Function₁ start) (hd : 𝚺₁-Function₁ stage) :
    𝚺₁-Predicate (fun k : M => k ≤ length → start k = target + stage k) := by
  haveI := hs
  haveI := hd
  definability

/-- The budget change of an entire encoded reference-occurrence chain equals
its independently summed binder depth, for nonstandard lengths as well. -/
theorem formulaReferenceChain_budget_suffix (nodes budgets length : M)
    (hchain : FormulaReferenceChain nodes budgets length) :
    ∀ k ≤ length, F PA194TargetStep.lookup ![F subCode ![length,k],budgets] =
      F PA194TargetStep.lookup ![length,budgets] + F chainDepth ![k,length,nodes] := by
  let start : M → M := fun k => F sourceChainStart ![k,length,budgets]
  let stage : M → M := fun k => F chainDepth ![k,length,nodes]
  let target := F PA194TargetStep.lookup ![length,budgets]
  have hs : 𝚺₁-Function₁ start := PA194CodeInstance.unary_of_three sourceChainStart length budgets
  have hd : 𝚺₁-Function₁ stage := PA194CodeInstance.unary_of_three chainDepth length nodes
  have hdef := budgetInvariant_definable start stage target length hs hd
  have hall : ∀ k : M, k ≤ length → start k = target + stage k := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _
      have hsub : F subCode ![length,0] = length := by
        have h := modelSubAdd (M := M) 0 length
        change F subCode ![(0 : M)+length,0] = length at h
        simpa only [zero_add] using h
      change F sourceChainStart ![0,length,budgets] = target + F chainDepth ![0,length,nodes]
      rw [sourceChainStart_model,hsub,chainDepth_zero,add_zero]
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
      obtain ⟨_,_,bit,hedge,hbudget⟩ := hchain d hj
      obtain ⟨choice,hchoice,hbit⟩ := directEdge_choice _ _ bit hedge
      have ih' := ih hk'
      change F sourceChainStart ![k,length,budgets] = target + F chainDepth ![k,length,nodes] at ih'
      rw [sourceChainStart_model,hsub0] at ih'
      change F sourceChainStart ![k+1,length,budgets] = target + F chainDepth ![k+1,length,nodes]
      rw [sourceChainStart_model,hsub1,chainDepth_succ,hsub1,hbit,hbudget,ih',add_assoc]
  intro k hk
  have h := hall k hk
  change F sourceChainStart ![k,length,budgets] = target + F chainDepth ![k,length,nodes] at h
  rwa [sourceChainStart_model] at h

theorem formulaReferenceChain_budget (nodes budgets length : M)
    (hchain : FormulaReferenceChain nodes budgets length) :
    F PA194TargetStep.lookup ![0,budgets] = F PA194TargetStep.lookup ![length,budgets] +
      F chainDepth ![length,length,nodes] := by
  have h := formulaReferenceChain_budget_suffix nodes budgets length hchain length (le_refl length)
  have hsub : F subCode ![length,length] = 0 := by
    have hz := modelSubAdd length (0 : M)
    change F subCode ![length+0,length] = 0 at hz
    simpa only [add_zero] using hz
  rwa [hsub] at h

#print axioms formulaReferenceChain_budget_suffix
#print axioms formulaReferenceChain_budget
#print axioms formulaReferenceEdge_and
#print axioms formulaReferenceEdge_or
#print axioms formulaReferenceEdge_all
#print axioms formulaReferenceEdge_ex
#print axioms formulaReferenceChain_coverage
end models
end PA194ModelLogic
