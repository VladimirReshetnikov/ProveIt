import PA194ModelRelExtReference
import PA194ModelFormulaTranslation
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
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance eqReflZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqReflOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqReflAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqReflMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqReflLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqReflIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqRefl : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

def sourceEqRefl : Sentence M6.PA.RelationalSource.language :=
  Theory.Eq.refl M6.PA.RelationalSource.language

noncomputable def eqReflRoot : M := ^∀ (^rel (2 : M) 0 (relExtVector 0 0))

theorem eqReflRoot_quote : (⌜sourceEqRefl⌝ : M) = eqReflRoot := by
  simp [Sentence.quote_def, sourceEqRefl, Theory.Eq.refl, eqReflRoot]
  change (⌜(Semiformula.rel M6.PA.RelationalSource.Relation.eq ![#0,#0] :
    Semiproposition M6.PA.RelationalSource.language 1)⌝ : M) = _
  simp [relExtVector, Matrix.vecHead, Matrix.vecTail, Function.comp_def, adjoin_def]
  rfl

theorem eqReflRoot_valid : IsUFormula M6.PA.RelationalSource.language (eqReflRoot (M := M)) := by
  simp only [eqReflRoot,IsUFormula.all,IsUFormula.rel]
  exact ⟨relExt_relation_zero,relExt_vector_valid 0 0⟩

theorem reference_pos_eq (params metadata b a c : M) :
    formulaReference params metadata (^rel (2 : M) 0 (relExtVector a c)) b =
      neighborhoodValue
        (F termLabelCode ![^#a,boundValue b params metadata,π₂ params])
        (F termLabelCode ![^#c,boundValue b params metadata,π₂ params])
        (π₂ (π₂ metadata)) := by
  have h := (formulaReference_recurrence params metadata).positive 0 (relExtVector a c) b
    relExt_relation_zero (relExt_vector_valid a c)
  change formulaReference params metadata (^rel (2 : M) 0 (relExtVector a c)) b = _ at h
  rw [h]
  simp only [atomValue, ite_true]
  change F equalityAtomCode ![^rel (2 : M) 0 (relExtVector a c),_,_,_] = _
  exact equalityAtom_model (^#a) (^#c) _ _ _

theorem eqRefl_reference_complete (b base reserve initial free : M) :
    formulaReference (pair initial free) (pair (b+1) (pair base reserve)) eqReflRoot (b+1) =
      allValue base (neighborhoodValue base base reserve) := by
  have hv : IsUFormula M6.PA.RelationalSource.language (^rel (2 : M) 0 (relExtVector 0 0)) := by
    simp only [IsUFormula.rel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 0 0⟩
  rw [eqReflRoot,reference_all _ _ _ _ hv,reference_pos_eq]
  simp only [pi₂_pair,termLabel_bound_nth]
  have hlabel : labelValue (b+1) (pair (b+1) (pair base reserve)) = base := by
    simpa only [add_zero] using labelValue_add (b+1) 0 base reserve
  have hbound : (boundValue b (pair initial free) (pair (b+1) (pair base reserve))).[0] = base := by
    rw [boundValue_add]
    have hone : (1 : M) = 0+1 := by simp
    rw [hone,allocateBound_succ,allocateBound_zero]
    simpa only [add_zero,←adjoin_def] using (nth_adjoin_zero base initial)
  rw [hlabel,hbound]

theorem eqReflRoot_budget_shape : ∃ b : M, eqReflRoot = b+1 := by
  have h : (0 : M)+1 ≤ (eqReflRoot (M := M)) := by
    change (0 : M)+1 ≤ pair (6 : M) (^rel (2 : M) 0 (relExtVector 0 0))+1
    have hz : (0 : M) ≤ pair (6 : M) (^rel (2 : M) 0 (relExtVector 0 0)) := zero_le
    simpa only [add_comm] using add_le_add_right hz 1
  obtain ⟨b,hb⟩ := le_iff_exists_add.mp h
  refine ⟨b,?_⟩
  simpa only [zero_add,add_comm] using hb

theorem fixedFormulaTranslation_eqRefl_target (initial free base reserve : M) :
    TargetProvable (F fixedFormulaTranslation ![(⌜sourceEqRefl⌝ : M),initial,free,base,reserve]) := by
  rw [eqReflRoot_quote]
  rw [fixedFormulaTranslation_correct _ _ _ _ _ eqReflRoot_valid]
  obtain ⟨b,hb⟩ := eqReflRoot_budget_shape (M := M)
  have h := eqRefl_reference_complete b base reserve initial free
  rw [←hb] at h
  rw [h]
  exact equality_reflexivity_supplier base reserve

#print axioms fixedFormulaTranslation_eqRefl_target
#print axioms eqRefl_reference_complete
#print axioms eqReflRoot_budget_shape
#print axioms eqReflRoot_quote
#print axioms eqReflRoot_valid
end models
end PA194ModelLogic
