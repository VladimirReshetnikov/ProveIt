import PA194ModelEqSymm
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
local instance eqTransZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqTransOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqTransAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqTransMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqTransLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqTransIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqTrans : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

def sourceEqTrans : Sentence M6.PA.RelationalSource.language :=
  Theory.Eq.trans M6.PA.RelationalSource.language

noncomputable def eqTransCore : M :=
  (^nrel (2 : M) 0 (relExtVector 2 1)) ^⋎
    ((^nrel (2 : M) 0 (relExtVector 1 0)) ^⋎ (^rel (2 : M) 0 (relExtVector 2 0)))
noncomputable def eqTransRoot : M := ^∀ (^∀ (^∀ eqTransCore))

theorem eqTransRoot_quote : (⌜sourceEqTrans⌝ : M) = eqTransRoot := by
  simp [Sentence.quote_def, sourceEqTrans, Theory.Eq.trans, eqTransRoot]
  change (⌜((Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#2,#1] ⋎
     (Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#1,#0] ⋎
      Semiformula.rel M6.PA.RelationalSource.Relation.eq ![#2,#0])) :
    Semiproposition M6.PA.RelationalSource.language 3)⌝ : M) = _
  simp [eqTransCore,relExtVector,Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  rfl

theorem eqTransCore_valid : IsUFormula M6.PA.RelationalSource.language (eqTransCore (M := M)) := by
  simp only [eqTransCore,IsUFormula.or,IsUFormula.nrel,IsUFormula.rel]
  exact ⟨⟨relExt_relation_zero,relExt_vector_valid 2 1⟩,
    ⟨⟨relExt_relation_zero,relExt_vector_valid 1 0⟩,⟨relExt_relation_zero,relExt_vector_valid 2 0⟩⟩⟩

theorem eqTransRoot_valid : IsUFormula M6.PA.RelationalSource.language (eqTransRoot (M := M)) := by
  simpa only [eqTransRoot,IsUFormula.all] using eqTransCore_valid (M := M)

theorem eqTrans_reference_complete (b base reserve initial free : M) :
    let ceiling := ((b+1)+1)+1
    let e₁ := neighborhoodValue base (base+1) reserve
    let e₂ := neighborhoodValue (base+1) ((base+1)+1) reserve
    let e₃ := neighborhoodValue base ((base+1)+1) reserve
    formulaReference (pair initial free) (pair ceiling (pair base reserve)) eqTransRoot ceiling =
      allValue base (allValue (base+1) (allValue ((base+1)+1)
        (impValue (negValue (negValue e₁)) (impValue (negValue (negValue e₂)) e₃)))) := by
  dsimp only
  have hn1 : IsUFormula M6.PA.RelationalSource.language (^nrel (2 : M) 0 (relExtVector 2 1)) := by
    simp only [IsUFormula.nrel]; exact ⟨relExt_relation_zero,relExt_vector_valid 2 1⟩
  have hn2 : IsUFormula M6.PA.RelationalSource.language (^nrel (2 : M) 0 (relExtVector 1 0)) := by
    simp only [IsUFormula.nrel]; exact ⟨relExt_relation_zero,relExt_vector_valid 1 0⟩
  have hp : IsUFormula M6.PA.RelationalSource.language (^rel (2 : M) 0 (relExtVector 2 0)) := by
    simp only [IsUFormula.rel]; exact ⟨relExt_relation_zero,relExt_vector_valid 2 0⟩
  have htail : IsUFormula M6.PA.RelationalSource.language
      ((^nrel (2 : M) 0 (relExtVector 1 0)) ^⋎ (^rel (2 : M) 0 (relExtVector 2 0))) := by
    simpa only [IsUFormula.or] using And.intro hn2 hp
  have h1 : IsUFormula M6.PA.RelationalSource.language (^∀ (eqTransCore (M := M))) := by
    simpa only [IsUFormula.all] using eqTransCore_valid (M := M)
  have h2 : IsUFormula M6.PA.RelationalSource.language (^∀ (^∀ (eqTransCore (M := M)))) := by
    simpa only [IsUFormula.all] using h1
  rw [eqTransRoot,reference_all _ _ _ _ h2,reference_all _ _ _ _ h1,
      reference_all _ _ _ _ eqTransCore_valid,eqTransCore,
      reference_or _ _ _ _ _ hn1 htail,reference_or _ _ _ _ _ hn2 hp,
      reference_neg_eq,reference_neg_eq,reference_pos_eq]
  simp only [pi₂_pair,termLabel_bound_nth]
  have hl0 : labelValue (((b+1)+1)+1) (pair (((b+1)+1)+1) (pair base reserve)) = base := by
    simpa only [add_zero] using labelValue_add (((b+1)+1)+1) 0 base reserve
  have hl1 : labelValue ((b+1)+1) (pair (((b+1)+1)+1) (pair base reserve)) = base+1 := by
    simpa only using labelValue_add ((b+1)+1) 1 base reserve
  have hl2 : labelValue (b+1) (pair (((b+1)+1)+1) (pair base reserve)) = (base+1)+1 := by
    simpa only [add_assoc] using labelValue_add (b+1) (1+1) base reserve
  have hs : let bound := boundValue b (pair initial free) (pair (((b+1)+1)+1) (pair base reserve))
      bound.[0] = (base+1)+1 ∧ bound.[1] = base+1 ∧ bound.[2] = base := by
    dsimp only
    have he : ((b+1)+1)+1 = b+(((0+1)+1)+1) := by simp [add_assoc]
    rw [he,boundValue_add]
    simp [allocateBound_succ,←adjoin_def]
    have hone : (1 : M) = 0+1 := by simp
    rw [hone,allocateBound_succ]
    simp [←adjoin_def,add_assoc]
  dsimp only at hs
  obtain ⟨hs0,hs1,hs2⟩ := hs
  rw [hl0,hl1,hl2,hs0,hs1,hs2]

theorem eqTransRoot_budget_shape : ∃ b : M, eqTransRoot = ((b+1)+1)+1 := by
  have ha (p : M) : p+1 ≤ ^∀ p := by
    change p+1 ≤ pair (6 : M) p+1
    simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) p) 1
  have hz : (0 : M) ≤ (eqTransCore (M := M)) := zero_le
  have h0 : (0 : M)+1 ≤ ^∀ (eqTransCore (M := M)) :=
    le_trans (by simpa only [add_comm] using add_le_add_right hz 1) (ha _)
  have h1 : ((0 : M)+1)+1 ≤ ^∀ (^∀ (eqTransCore (M := M))) :=
    le_trans (by simpa only [add_comm] using add_le_add_right h0 1) (ha _)
  have h2 : (((0 : M)+1)+1)+1 ≤ (eqTransRoot (M := M)) := by
    simpa only [eqTransRoot] using le_trans (by simpa only [add_comm] using add_le_add_right h1 1) (ha _)
  obtain ⟨b,hb⟩ := le_iff_exists_add.mp h2
  exact ⟨b, by simpa only [zero_add,add_assoc,add_comm,add_left_comm] using hb⟩

theorem fixedFormulaTranslation_eqTrans_target (initial free base reserve : M) :
    TargetProvable (F fixedFormulaTranslation ![(⌜sourceEqTrans⌝ : M),initial,free,base,reserve]) := by
  rw [eqTransRoot_quote]
  rw [fixedFormulaTranslation_correct _ _ _ _ _ eqTransRoot_valid]
  obtain ⟨b,hb⟩ := eqTransRoot_budget_shape (M := M)
  have h := eqTrans_reference_complete b base reserve initial free
  dsimp only at h
  rw [←hb] at h
  rw [h]
  exact equality_transitivity_supplier base reserve

#print axioms fixedFormulaTranslation_eqTrans_target
#print axioms eqTrans_reference_complete
#print axioms eqTransRoot_budget_shape
#print axioms eqTransRoot_quote
#print axioms eqTransRoot_valid
end models
end PA194ModelLogic
