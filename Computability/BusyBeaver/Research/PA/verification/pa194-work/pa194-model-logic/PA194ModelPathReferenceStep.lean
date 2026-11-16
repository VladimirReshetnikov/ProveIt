import PA194ModelPathGraph

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

theorem select_is_child (choice p q : M) : F selectCode ![choice,p,q] = p ∨ F selectCode ![choice,p,q] = q := by
  rcases zero_or_succ choice with (rfl | ⟨j,rfl⟩)
  · right
    have hz := modelSelectZero (M := M) p q
    change F selectCode ![(0 : M),p,q] = q at hz
    exact hz
  · left
    have hs := modelSelectSucc (M := M) j p q
    change F selectCode ![F Code.succ (fun _ => j),p,q] = p at hs
    rw [modelSucc] at hs
    exact hs

/-- A valid source node either stutters at a leaf with bit zero or follows an
independent syntactic constructor edge with its exact binder bit. -/
theorem validSourceChild_step (parent choice : M)
    (hp : IsUFormula M6.PA.RelationalSource.language parent) :
    (F sourceChild ![parent,choice] = parent ∧ F binderBit ![parent] = 0) ∨
      SourceDirectEdge parent (F sourceChild ![parent,choice]) (F binderBit ![parent]) := by
  rcases IsUFormula.case hp with (⟨k,r,v,hr,hv,rfl⟩ | ⟨k,r,v,hr,hv,rfl⟩ | rfl | rfl |
      ⟨a,b,ha,hb,rfl⟩ | ⟨a,b,ha,hb,rfl⟩ | ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩)
  · left
    constructor
    · simpa only [qqRel] using sourceChild_leaf (0 : M) (pair k (pair r v)) choice (Or.inl rfl)
    · change F binderBit ![pair (0 : M) (pair k (pair r v))+1] = 0
      rw [binderBit_model,nodeTag_model]; norm_num
  · left
    constructor
    · simpa only [qqNRel] using sourceChild_leaf (1 : M) (pair k (pair r v)) choice (Or.inr (Or.inl rfl))
    · change F binderBit ![pair (1 : M) (pair k (pair r v))+1] = 0
      rw [binderBit_model,nodeTag_model]; norm_num
  · left
    constructor
    · simpa only [qqVerum] using sourceChild_leaf (2 : M) 0 choice (Or.inr (Or.inr (Or.inl rfl)))
    · change F binderBit ![pair (2 : M) 0+1] = 0
      rw [binderBit_model,nodeTag_model]; norm_num
  · left
    constructor
    · simpa only [qqFalsum] using sourceChild_leaf (3 : M) 0 choice (Or.inr (Or.inr (Or.inr rfl)))
    · change F binderBit ![pair (3 : M) 0+1] = 0
      rw [binderBit_model,nodeTag_model]; norm_num
  · right
    change SourceDirectEdge (pair (4 : M) (pair a b)+1)
      (F sourceChild ![pair (4 : M) (pair a b)+1,choice])
      (F binderBit ![pair (4 : M) (pair a b)+1])
    have hbit : F binderBit ![pair (4 : M) (pair a b)+1] = 0 := by
      rw [binderBit_model,nodeTag_model]; norm_num
    rw [hbit,sourceChild_binary (4 : M) a b choice (Or.inl rfl)]
    rcases select_is_child choice a b with hs | hs
    · rw [hs]; exact Or.inl ⟨a,b,rfl,Or.inl rfl,rfl⟩
    · rw [hs]; exact Or.inl ⟨a,b,rfl,Or.inr rfl,rfl⟩
  · right
    change SourceDirectEdge (pair (5 : M) (pair a b)+1)
      (F sourceChild ![pair (5 : M) (pair a b)+1,choice])
      (F binderBit ![pair (5 : M) (pair a b)+1])
    have hbit : F binderBit ![pair (5 : M) (pair a b)+1] = 0 := by
      rw [binderBit_model,nodeTag_model]; norm_num
    rw [hbit,sourceChild_binary (5 : M) a b choice (Or.inr rfl)]
    rcases select_is_child choice a b with hs | hs
    · rw [hs]; exact Or.inr (Or.inl ⟨a,b,rfl,Or.inl rfl,rfl⟩)
    · rw [hs]; exact Or.inr (Or.inl ⟨a,b,rfl,Or.inr rfl,rfl⟩)
  · right
    change SourceDirectEdge (pair (6 : M) a+1) (F sourceChild ![pair (6 : M) a+1,choice])
      (F binderBit ![pair (6 : M) a+1])
    have hbit : F binderBit ![pair (6 : M) a+1] = 1 := by rw [binderBit_model,nodeTag_model]; norm_num
    rw [hbit,sourceChild_binder (6 : M) a choice (Or.inl rfl)]
    exact Or.inr (Or.inr (Or.inl ⟨a,rfl,rfl,rfl⟩))
  · right
    change SourceDirectEdge (pair (7 : M) a+1) (F sourceChild ![pair (7 : M) a+1,choice])
      (F binderBit ![pair (7 : M) a+1])
    have hbit : F binderBit ![pair (7 : M) a+1] = 1 := by rw [binderBit_model,nodeTag_model]; norm_num
    rw [hbit,sourceChild_binder (7 : M) a choice (Or.inr rfl)]
    exact Or.inr (Or.inr (Or.inr ⟨a,rfl,rfl,rfl⟩))

/-- Along a path from valid syntax, every model-valued step either stutters at
a leaf with unchanged budget or is an edge of the explicit reference recursion. -/
theorem path_reference_step (root choices i : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root) :
    (F sourcePath ![i+1,root,choices] = F sourcePath ![i,root,choices] ∧
      F pathRemaining ![i+1,root,choices] = F pathRemaining ![i,root,choices]) ∨
    FormulaReferenceEdge (F sourcePath ![i,root,choices]) (F pathRemaining ![i,root,choices])
      (F sourcePath ![i+1,root,choices]) (F pathRemaining ![i+1,root,choices]) := by
  have hp := sourcePath_preserves_formula root choices i hroot
  have hc := sourcePath_preserves_formula root choices (i+1) hroot
  have hn := sourcePath_succ i root choices
  have he := validSourceChild_step (F sourcePath ![i,root,choices])
    (F PA194TargetStep.lookup ![i,choices]) hp
  rcases he with ⟨hstutter,hbit⟩ | hedge
  · left
    constructor
    · rw [hn,hstutter]
    · have hb := path_remaining_nonbinder root choices i hbit
      simpa only [pathRemaining_model] using hb
  · right
    refine ⟨hp,hc,F binderBit ![F sourcePath ![i,root,choices]],?_,?_⟩
    · rw [hn]
      exact hedge
    · have hb := path_remaining_step root choices i
      have hb' : F pathRemaining ![i+1,root,choices] +
          F binderBit ![F sourcePath ![i,root,choices]] =
          F pathRemaining ![i,root,choices] := by
        simpa only [pathRemaining_model] using hb
      exact hb'.symm

/-- The endpoints of that step are actual Foundation graph entries. -/
theorem path_reference_graph_step (root choices i params metadata : M)
    (hroot : IsUFormula M6.PA.RelationalSource.language root) :
    (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (F pathRemaining ![i,root,choices]) (pair params metadata))
      (F sourcePath ![i,root,choices])
      (formulaReference params metadata (F sourcePath ![i,root,choices])
        (F pathRemaining ![i,root,choices])) ∧
    (formulaConstruction (M := M)).Graph M6.PA.RelationalSource.language
      (pair (F pathRemaining ![i+1,root,choices]) (pair params metadata))
      (F sourcePath ![i+1,root,choices])
      (formulaReference params metadata (F sourcePath ![i+1,root,choices])
        (F pathRemaining ![i+1,root,choices])) ∧
    ((F sourcePath ![i+1,root,choices] = F sourcePath ![i,root,choices] ∧
      F pathRemaining ![i+1,root,choices] = F pathRemaining ![i,root,choices]) ∨
    FormulaReferenceEdge (F sourcePath ![i,root,choices]) (F pathRemaining ![i,root,choices])
      (F sourcePath ![i+1,root,choices]) (F pathRemaining ![i+1,root,choices])) := by
  exact ⟨path_reference_graph root choices i params metadata hroot,
    path_reference_graph root choices (i+1) params metadata hroot,
    path_reference_step root choices i hroot⟩

#print axioms path_reference_step
#print axioms path_reference_graph_step
#print axioms validSourceChild_step
end models
end PA194ModelLogic
