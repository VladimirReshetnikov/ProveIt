import PA194ModelRelExtBudget
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance relExtSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance relExtSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance relExtSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance relExtSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance relExtSourceLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance relExtSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def relExtVector (a b : M) := pair (^#a) (pair (^#b) 0+1)+1
noncomputable def relExtNegEq1 : M := ^nrel (2 : M) (0 : M) (relExtVector 0 2)
noncomputable def relExtNegEq2 : M := ^nrel (2 : M) (0 : M) (relExtVector 1 3)
noncomputable def relExtNegMem : M := ^nrel (2 : M) (1 : M) (relExtVector 0 1)
noncomputable def relExtPosMem : M := ^rel (2 : M) (1 : M) (relExtVector 2 3)
noncomputable def relExtCore : M :=
  (relExtNegEq1 ^⋎ (relExtNegEq2 ^⋎ ^⊥)) ^⋎ (relExtNegMem ^⋎ relExtPosMem)
noncomputable def relExtRoot : M := ^∀ (^∀ (^∀ (^∀ relExtCore)))

theorem relExt_vector_valid (a b : M) :
    IsUTermVec M6.PA.RelationalSource.language 2 (relExtVector a b) := by
  apply IsUTermVec.two_iff.mpr
  refine ⟨^#a,^#b,?_,?_,rfl⟩ <;> simp

theorem relExt_relation_zero : M6.PA.RelationalSource.language.IsRel (2 : M) (0 : M) := by
  change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),(0 : M)])
  simp

theorem relExt_relation_one : M6.PA.RelationalSource.language.IsRel (2 : M) (1 : M) := by
  change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),(1 : M)])
  simp

theorem relExtCore_valid : IsUFormula M6.PA.RelationalSource.language (relExtCore (M := M)) := by
  simp only [relExtCore,IsUFormula.or,relExtNegEq1,relExtNegEq2,relExtNegMem,relExtPosMem,
    IsUFormula.nrel,IsUFormula.rel,IsUFormula.falsum]
  exact ⟨⟨⟨relExt_relation_zero,relExt_vector_valid 0 2⟩,
    ⟨⟨relExt_relation_zero,relExt_vector_valid 1 3⟩,True.intro⟩⟩,
    ⟨⟨relExt_relation_one,relExt_vector_valid 0 1⟩,⟨relExt_relation_one,relExt_vector_valid 2 3⟩⟩⟩

theorem relExtRoot_valid : IsUFormula M6.PA.RelationalSource.language (relExtRoot (M := M)) := by
  simpa only [relExtRoot,IsUFormula.all] using relExtCore_valid (M := M)

theorem relExtRoot_quote : (⌜PA194RelExtTypedTranslation.sourceRelExt⌝ : M) = relExtRoot := by
  simp [Sentence.quote_def, PA194RelExtTypedTranslation.sourceRelExt,
    Theory.Eq.relExt, allClosure, Semiformula.quote_all, relExtRoot]
  change (⌜(((Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#0,#2] ⋎
    (Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#1,#3] ⋎ ⊥)) ⋎
    (Semiformula.nrel M6.PA.RelationalSource.Relation.mem ![#0,#1] ⋎
     Semiformula.rel M6.PA.RelationalSource.Relation.mem ![#2,#3])) :
       Semiproposition M6.PA.RelationalSource.language 4)⌝ : M) = _
  simp [relExtCore, relExtNegEq1, relExtNegEq2, relExtNegMem, relExtPosMem, relExtVector, Matrix.vecHead, Matrix.vecTail,
    Function.comp_def, adjoin_def]
  constructor
  · rfl
  · change ((1 : ℕ) : M) = 1
    simp


#print axioms relExtRoot_quote
#print axioms relExtRoot_valid
#print axioms relExtCore_valid
end models
end PA194ModelLogic
