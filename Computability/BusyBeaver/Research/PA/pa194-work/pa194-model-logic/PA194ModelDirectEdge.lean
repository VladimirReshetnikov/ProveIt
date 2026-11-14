import PA194ModelPathReachabilityDef

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

/-- Independent immediate syntactic-child relation, with binder bit, defined by
source constructor encodings rather than by operational sourcePath reachability. -/
def SourceDirectEdge (parent child binder : M) : Prop :=
  (∃ p q, parent = pair (4 : M) (pair p q)+1 ∧ (child=p ∨ child=q) ∧ binder=0) ∨
  (∃ p q, parent = pair (5 : M) (pair p q)+1 ∧ (child=p ∨ child=q) ∧ binder=0) ∨
  (∃ p, parent = pair (6 : M) p+1 ∧ child=p ∧ binder=1) ∨
  (∃ p, parent = pair (7 : M) p+1 ∧ child=p ∧ binder=1)

theorem directEdge_choice (parent child binder : M) (h : SourceDirectEdge parent child binder) :
    ∃ choice, F sourceChild ![parent,choice] = child ∧ F binderBit ![parent] = binder := by
  rcases h with (⟨p,q,rfl,hchild,rfl⟩ | ⟨p,q,rfl,hchild,rfl⟩ |
    ⟨p,rfl,rfl,rfl⟩ | ⟨p,rfl,rfl,rfl⟩)
  · rcases hchild with rfl | rfl
    · refine ⟨1,?_,?_⟩
      · rw [sourceChild_binary (4 : M) child q 1 (Or.inl rfl)]
        exact modelSelect_ne_zero 1 child q (by simp)
      · rw [binderBit_model,nodeTag_model]; norm_num
    · refine ⟨0,?_,?_⟩
      · rw [sourceChild_binary (4 : M) p child 0 (Or.inl rfl)]
        have hz := modelSelectZero (M := M) p child
        change F selectCode ![(0 : M),p,child] = child at hz
        exact hz
      · rw [binderBit_model,nodeTag_model]; norm_num
  · rcases hchild with rfl | rfl
    · refine ⟨1,?_,?_⟩
      · rw [sourceChild_binary (5 : M) child q 1 (Or.inr rfl)]
        exact modelSelect_ne_zero 1 child q (by simp)
      · rw [binderBit_model,nodeTag_model]; norm_num
    · refine ⟨0,?_,?_⟩
      · rw [sourceChild_binary (5 : M) p child 0 (Or.inr rfl)]
        have hz := modelSelectZero (M := M) p child
        change F selectCode ![(0 : M),p,child] = child at hz
        exact hz
      · rw [binderBit_model,nodeTag_model]; norm_num
  · refine ⟨0,sourceChild_binder (6 : M) child 0 (Or.inl rfl),?_⟩
    rw [binderBit_model,nodeTag_model]; norm_num
  · refine ⟨0,sourceChild_binder (7 : M) child 0 (Or.inr rfl),?_⟩
    rw [binderBit_model,nodeTag_model]; norm_num

theorem directEdge_extend_path (parent child target binder depth : M)
    (h : SourceDirectEdge parent child binder) (hp : PathWithDepth child target depth) :
    PathWithDepth parent target (binder+depth) := by
  obtain ⟨choice,hc,hb⟩ := directEdge_choice parent child binder h
  have hh := pathWithDepth_extend parent child target depth choice hc hp
  rwa [hb] at hh

#print axioms directEdge_choice
#print axioms directEdge_extend_path
end models
end PA194ModelLogic
