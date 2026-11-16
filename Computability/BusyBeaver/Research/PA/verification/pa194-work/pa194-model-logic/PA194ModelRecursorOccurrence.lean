import PA194ModelDescendantComplexity

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

/-- Every single recursive input in the independent Foundation formula recursion
is a chain-defined descendant, with its actual binder depth. -/
theorem edge_immediate_occurrence (parent child bit : M) (he : SourceDirectEdge parent child bit) :
    CodedSyntacticDescendant parent child ∧ PathWithDepth parent child bit := by
  constructor
  · exact codedSyntacticDescendant_extend parent child child bit he (codedSyntacticDescendant_self child)
  · have hp := directEdge_extend_path parent child child bit 0 he (pathWithDepth_self child)
    simpa only [add_zero] using hp

theorem formulaReference_and_occurrences (p q b params metadata : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    let root := pair (4 : M) (pair p q)+1
    (CodedSyntacticDescendant root p ∧ PathWithDepth root p 0) ∧
    (CodedSyntacticDescendant root q ∧ PathWithDepth root q 0) ∧
    formulaReference params metadata root b =
      conjValue (formulaReference params metadata p b) (formulaReference params metadata q b) := by
  dsimp only
  have hl : SourceDirectEdge (pair (4 : M) (pair p q)+1) p 0 :=
    Or.inl ⟨p,q,rfl,Or.inl rfl,rfl⟩
  have hr : SourceDirectEdge (pair (4 : M) (pair p q)+1) q 0 :=
    Or.inl ⟨p,q,rfl,Or.inr rfl,rfl⟩
  exact ⟨edge_immediate_occurrence _ _ _ hl,edge_immediate_occurrence _ _ _ hr,
    (formulaReference_recurrence params metadata).andRule p q b hp hq⟩

theorem formulaReference_or_occurrences (p q b params metadata : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    let root := pair (5 : M) (pair p q)+1
    (CodedSyntacticDescendant root p ∧ PathWithDepth root p 0) ∧
    (CodedSyntacticDescendant root q ∧ PathWithDepth root q 0) ∧
    formulaReference params metadata root b =
      impValue (negValue (formulaReference params metadata p b)) (formulaReference params metadata q b) := by
  dsimp only
  have hl : SourceDirectEdge (pair (5 : M) (pair p q)+1) p 0 :=
    Or.inr (Or.inl ⟨p,q,rfl,Or.inl rfl,rfl⟩)
  have hr : SourceDirectEdge (pair (5 : M) (pair p q)+1) q 0 :=
    Or.inr (Or.inl ⟨p,q,rfl,Or.inr rfl,rfl⟩)
  exact ⟨edge_immediate_occurrence _ _ _ hl,edge_immediate_occurrence _ _ _ hr,
    (formulaReference_recurrence params metadata).orRule p q b hp hq⟩

theorem formulaReference_all_occurrence (p b params metadata : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    let root := pair (6 : M) p+1
    (CodedSyntacticDescendant root p ∧ PathWithDepth root p 1) ∧
    formulaReference params metadata root (b+1) =
      allValue (labelValue (b+1) metadata) (formulaReference params metadata p b) := by
  dsimp only
  have he : SourceDirectEdge (pair (6 : M) p+1) p 1 := Or.inr (Or.inr (Or.inl ⟨p,rfl,rfl,rfl⟩))
  exact ⟨edge_immediate_occurrence _ _ _ he,(formulaReference_recurrence params metadata).allRule p b hp⟩

theorem formulaReference_ex_occurrence (p b params metadata : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    let root := pair (7 : M) p+1
    (CodedSyntacticDescendant root p ∧ PathWithDepth root p 1) ∧
    formulaReference params metadata root (b+1) =
      exValue (labelValue (b+1) metadata) (formulaReference params metadata p b) := by
  dsimp only
  have he : SourceDirectEdge (pair (7 : M) p+1) p 1 := Or.inr (Or.inr (Or.inr ⟨p,rfl,rfl,rfl⟩))
  exact ⟨edge_immediate_occurrence _ _ _ he,(formulaReference_recurrence params metadata).exRule p b hp⟩

#print axioms formulaReference_and_occurrences
#print axioms formulaReference_or_occurrences
#print axioms formulaReference_all_occurrence
#print axioms formulaReference_ex_occurrence
end models
end PA194ModelLogic
