import PA194ModelRecursorChain

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

/-- A real Foundation fixpoint-graph conjunction entry exposes both child graph
entries and both newly specified reference-recursion edges. -/
theorem formulaGraph_and_occurrences (p q b params metadata y : M)
    (h : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (pair (4 : M) (pair p q)+1) y) :
    ∃ y₁ y₂ : M,
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p y₁ ∧
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) q y₂ ∧
      FormulaReferenceEdge (pair (4 : M) (pair p q)+1) b p b ∧
      FormulaReferenceEdge (pair (4 : M) (pair p q)+1) b q b := by
  have hv := (formulaConstruction (M := M)).graph_dom_uformula h
  have hv' : IsUFormula M6.PA.RelationalSource.language (p ^⋏ q) := by simpa only [qqAnd] using hv
  obtain ⟨hp,hq⟩ := IsUFormula.and.mp hv'
  have hg : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (p ^⋏ q) y := by simpa only [qqAnd] using h
  obtain ⟨y₁,y₂,h₁,h₂,hy⟩ := (formulaConstruction (M := M)).graph_and_inv hg
  exact ⟨y₁,y₂,h₁,h₂,(formulaReferenceEdge_and p q b hp hq).1,
    (formulaReferenceEdge_and p q b hp hq).2⟩

theorem formulaGraph_or_occurrences (p q b params metadata y : M)
    (h : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (pair (5 : M) (pair p q)+1) y) :
    ∃ y₁ y₂ : M,
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p y₁ ∧
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) q y₂ ∧
      FormulaReferenceEdge (pair (5 : M) (pair p q)+1) b p b ∧
      FormulaReferenceEdge (pair (5 : M) (pair p q)+1) b q b := by
  have hv := (formulaConstruction (M := M)).graph_dom_uformula h
  have hv' : IsUFormula M6.PA.RelationalSource.language (p ^⋎ q) := by simpa only [qqOr] using hv
  obtain ⟨hp,hq⟩ := IsUFormula.or.mp hv'
  have hg : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (p ^⋎ q) y := by simpa only [qqOr] using h
  obtain ⟨y₁,y₂,h₁,h₂,hy⟩ := (formulaConstruction (M := M)).graph_or_inv hg
  exact ⟨y₁,y₂,h₁,h₂,(formulaReferenceEdge_or p q b hp hq).1,
    (formulaReferenceEdge_or p q b hp hq).2⟩

/-- A positive-budget graph binder exposes the body graph at the actual
changed Foundation parameter and hence a one-binder reference edge. -/
theorem formulaGraph_all_occurrence (p b params metadata y : M)
    (h : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (b+1) (pair params metadata)) (pair (6 : M) p+1) y) :
    ∃ y₁ : M,
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p y₁ ∧
      FormulaReferenceEdge (pair (6 : M) p+1) (b+1) p b := by
  have hv := (formulaConstruction (M := M)).graph_dom_uformula h
  have hv' : IsUFormula M6.PA.RelationalSource.language (^∀ p) := by simpa only [qqAll] using hv
  have hp := IsUFormula.all.mp hv'
  have hg : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (b+1) (pair params metadata)) (^∀ p) y := by simpa only [qqAll] using h
  obtain ⟨y₁,hc,hy⟩ := (formulaConstruction (M := M)).graph_all_inv hg
  have hchange : (formulaConstruction (M := M)).allChanges (pair (b+1) (pair params metadata)) =
      pair b (pair params metadata) := by
    change F specChange ![pair (b+1) (pair params metadata)] = _
    exact specChange_model b params metadata
  rw [hchange] at hc
  exact ⟨y₁,hc,formulaReferenceEdge_all p b hp⟩

theorem formulaGraph_ex_occurrence (p b params metadata y : M)
    (h : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (b+1) (pair params metadata)) (pair (7 : M) p+1) y) :
    ∃ y₁ : M,
      (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
        (pair b (pair params metadata)) p y₁ ∧
      FormulaReferenceEdge (pair (7 : M) p+1) (b+1) p b := by
  have hv := (formulaConstruction (M := M)).graph_dom_uformula h
  have hv' : IsUFormula M6.PA.RelationalSource.language (^∃ p) := by simpa only [qqExs] using hv
  have hp := IsUFormula.ex.mp hv'
  have hg : (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (b+1) (pair params metadata)) (^∃ p) y := by simpa only [qqExs] using h
  obtain ⟨y₁,hc,hy⟩ := (formulaConstruction (M := M)).graph_ex_inv hg
  have hchange : (formulaConstruction (M := M)).exsChanges (pair (b+1) (pair params metadata)) =
      pair b (pair params metadata) := by
    change F specChange ![pair (b+1) (pair params metadata)] = _
    exact specChange_model b params metadata
  rw [hchange] at hc
  exact ⟨y₁,hc,formulaReferenceEdge_ex p b hp⟩

#print axioms formulaGraph_all_occurrence
#print axioms formulaGraph_ex_occurrence
#print axioms formulaGraph_and_occurrences
#print axioms formulaGraph_or_occurrences
end models
end PA194ModelLogic
