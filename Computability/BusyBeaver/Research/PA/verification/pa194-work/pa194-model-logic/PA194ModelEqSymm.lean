import PA194ModelEqRefl
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
local instance eqSymmZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqSymmOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqSymmAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqSymmMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqSymmLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqSymmIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqSymm : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

def sourceEqSymm : Sentence M6.PA.RelationalSource.language :=
  Theory.Eq.symm M6.PA.RelationalSource.language

noncomputable def eqSymmCore : M :=
  (^nrel (2 : M) 0 (relExtVector 1 0)) ^⋎ (^rel (2 : M) 0 (relExtVector 0 1))
noncomputable def eqSymmRoot : M := ^∀ (^∀ eqSymmCore)

theorem eqSymmRoot_quote : (⌜sourceEqSymm⌝ : M) = eqSymmRoot := by
  simp [Sentence.quote_def, sourceEqSymm, Theory.Eq.symm, eqSymmRoot]
  change (⌜((Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#1,#0] ⋎
     Semiformula.rel M6.PA.RelationalSource.Relation.eq ![#0,#1]) :
    Semiproposition M6.PA.RelationalSource.language 2)⌝ : M) = _
  simp [eqSymmCore,relExtVector,Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  rfl

theorem eqSymmCore_valid : IsUFormula M6.PA.RelationalSource.language (eqSymmCore (M := M)) := by
  simp only [eqSymmCore,IsUFormula.or,IsUFormula.nrel,IsUFormula.rel]
  exact ⟨⟨relExt_relation_zero,relExt_vector_valid 1 0⟩,⟨relExt_relation_zero,relExt_vector_valid 0 1⟩⟩

theorem eqSymmRoot_valid : IsUFormula M6.PA.RelationalSource.language (eqSymmRoot (M := M)) := by
  simpa only [eqSymmRoot,IsUFormula.all] using eqSymmCore_valid (M := M)

theorem eqSymm_reference_complete (b base reserve initial free : M) :
    let ceiling := (b+1)+1
    let e₁ := neighborhoodValue base (base+1) reserve
    let e₂ := neighborhoodValue (base+1) base reserve
    formulaReference (pair initial free) (pair ceiling (pair base reserve)) eqSymmRoot ceiling =
      allValue base (allValue (base+1) (impValue (negValue (negValue e₁)) e₂)) := by
  dsimp only
  have hneg : IsUFormula M6.PA.RelationalSource.language (^nrel (2 : M) 0 (relExtVector 1 0)) := by
    simp only [IsUFormula.nrel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 1 0⟩
  have hpos : IsUFormula M6.PA.RelationalSource.language (^rel (2 : M) 0 (relExtVector 0 1)) := by
    simp only [IsUFormula.rel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 0 1⟩
  have hbinder : IsUFormula M6.PA.RelationalSource.language (^∀ (eqSymmCore (M := M))) := by
    simpa only [IsUFormula.all] using eqSymmCore_valid (M := M)
  rw [eqSymmRoot,reference_all _ _ _ _ hbinder,reference_all _ _ _ _ eqSymmCore_valid,
      eqSymmCore,reference_or _ _ _ _ _ hneg hpos,reference_neg_eq,reference_pos_eq]
  simp only [pi₂_pair,termLabel_bound_nth]
  have h0 : labelValue ((b+1)+1) (pair ((b+1)+1) (pair base reserve)) = base := by
    simpa only [add_zero] using labelValue_add ((b+1)+1) 0 base reserve
  have h1 : labelValue (b+1) (pair ((b+1)+1) (pair base reserve)) = base+1 := by
    simpa only using labelValue_add (b+1) 1 base reserve
  have hs : let bound := boundValue b (pair initial free) (pair ((b+1)+1) (pair base reserve))
      bound.[0] = base+1 ∧ bound.[1] = base := by
    dsimp only
    have he : (b+1)+1 = b+((0+1)+1) := by simp [add_assoc]
    rw [he,boundValue_add]
    simp [allocateBound_succ,←adjoin_def]
    have hone : (1 : M) = 0+1 := by simp
    rw [hone,allocateBound_succ]
    simp [←adjoin_def]
  dsimp only at hs
  obtain ⟨hs0,hs1⟩ := hs
  rw [h0,h1,hs0,hs1]

theorem eqSymmRoot_budget_shape : ∃ b : M, eqSymmRoot = (b+1)+1 := by
  have ha (p : M) : p+1 ≤ ^∀ p := by
    change p+1 ≤ pair (6 : M) p+1
    simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) p) 1
  have hz : (0 : M) ≤ (eqSymmCore (M := M)) := zero_le
  have h0 : (0 : M)+1 ≤ ^∀ (eqSymmCore (M := M)) :=
    le_trans (by simpa only [add_comm] using add_le_add_right hz 1) (ha _)
  have h1 : ((0 : M)+1)+1 ≤ (eqSymmRoot (M := M)) := by
    simpa only [eqSymmRoot] using le_trans (by simpa only [add_comm] using add_le_add_right h0 1) (ha _)
  obtain ⟨b,hb⟩ := le_iff_exists_add.mp h1
  exact ⟨b, by simpa only [zero_add,add_assoc,add_comm,add_left_comm] using hb⟩

theorem fixedFormulaTranslation_eqSymm_target (initial free base reserve : M) :
    TargetProvable (F fixedFormulaTranslation ![(⌜sourceEqSymm⌝ : M),initial,free,base,reserve]) := by
  rw [eqSymmRoot_quote]
  rw [fixedFormulaTranslation_correct _ _ _ _ _ eqSymmRoot_valid]
  obtain ⟨b,hb⟩ := eqSymmRoot_budget_shape (M := M)
  have h := eqSymm_reference_complete b base reserve initial free
  dsimp only at h
  rw [←hb] at h
  rw [h]
  exact equality_symmetry_supplier base reserve

#print axioms fixedFormulaTranslation_eqSymm_target
#print axioms eqSymm_reference_complete
#print axioms eqSymmRoot_budget_shape
#print axioms eqSymmRoot_quote
#print axioms eqSymmRoot_valid
end models
end PA194ModelLogic
