import PA194ModelEqTrans
import PA194ModelEqualityRelExtSupplier
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
local instance eqRelExtZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqRelExtOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqRelExtAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqRelExtMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqRelExtLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqRelExtIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqRelExt : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

def sourceEqRelExt : Sentence M6.PA.RelationalSource.language :=
  Theory.Eq.relExt (L := M6.PA.RelationalSource.language) M6.PA.RelationalSource.Relation.eq

noncomputable def eqRelExtNegOld : M := ^nrel (2 : M) 0 (relExtVector 0 1)
noncomputable def eqRelExtPosNew : M := ^rel (2 : M) 0 (relExtVector 2 3)
noncomputable def eqRelExtCore : M :=
  (relExtNegEq1 ^⋎ (relExtNegEq2 ^⋎ ^⊥)) ^⋎ (eqRelExtNegOld ^⋎ eqRelExtPosNew)
noncomputable def eqRelExtRoot : M := ^∀ (^∀ (^∀ (^∀ eqRelExtCore)))

theorem eqRelExtRoot_quote : (⌜sourceEqRelExt⌝ : M) = eqRelExtRoot := by
  simp [Sentence.quote_def, sourceEqRelExt, Theory.Eq.relExt, allClosure, eqRelExtRoot]
  change (⌜(((Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#0,#2] ⋎
    (Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#1,#3] ⋎ ⊥)) ⋎
    (Semiformula.nrel M6.PA.RelationalSource.Relation.eq ![#0,#1] ⋎
     Semiformula.rel M6.PA.RelationalSource.Relation.eq ![#2,#3])) :
       Semiproposition M6.PA.RelationalSource.language 4)⌝ : M) = _
  simp [eqRelExtCore,eqRelExtNegOld,eqRelExtPosNew,relExtNegEq1,relExtNegEq2,
    relExtVector,Matrix.vecHead,Matrix.vecTail,Function.comp_def,adjoin_def]
  rfl

theorem eqRelExtCore_valid : IsUFormula M6.PA.RelationalSource.language (eqRelExtCore (M := M)) := by
  simp only [eqRelExtCore,relExtNegEq1,relExtNegEq2,eqRelExtNegOld,eqRelExtPosNew,
    IsUFormula.or,IsUFormula.nrel,IsUFormula.rel,IsUFormula.falsum]
  exact ⟨⟨⟨relExt_relation_zero,relExt_vector_valid 0 2⟩,
    ⟨⟨relExt_relation_zero,relExt_vector_valid 1 3⟩,True.intro⟩⟩,
    ⟨⟨relExt_relation_zero,relExt_vector_valid 0 1⟩,⟨relExt_relation_zero,relExt_vector_valid 2 3⟩⟩⟩

theorem eqRelExtRoot_valid : IsUFormula M6.PA.RelationalSource.language (eqRelExtRoot (M := M)) := by
  simpa only [eqRelExtRoot,IsUFormula.all] using eqRelExtCore_valid (M := M)

theorem eqRelExt_reference_core (params metadata b : M) :
    let bound := boundValue b params metadata
    let z := π₂ (π₂ metadata)
    let e₁ := neighborhoodValue bound.[0] bound.[2] z
    let e₂ := neighborhoodValue bound.[1] bound.[3] z
    let old := neighborhoodValue bound.[0] bound.[1] z
    let new := neighborhoodValue bound.[2] bound.[3] z
    formulaReference params metadata eqRelExtCore b =
      impValue (negValue (impValue (negValue (negValue e₁))
        (impValue (negValue (negValue e₂)) (memValue 0 0))))
        (impValue (negValue (negValue old)) new) := by
  have he1 : IsUFormula M6.PA.RelationalSource.language (relExtNegEq1 (M := M)) := by
    simp only [relExtNegEq1,IsUFormula.nrel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 0 2⟩
  have he2 : IsUFormula M6.PA.RelationalSource.language (relExtNegEq2 (M := M)) := by
    simp only [relExtNegEq2,IsUFormula.nrel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 1 3⟩
  have hm1 : IsUFormula M6.PA.RelationalSource.language (eqRelExtNegOld (M := M)) := by
    simp only [eqRelExtNegOld,IsUFormula.nrel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 0 1⟩
  have hm2 : IsUFormula M6.PA.RelationalSource.language (eqRelExtPosNew (M := M)) := by
    simp only [eqRelExtPosNew,IsUFormula.rel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 2 3⟩
  have hf : IsUFormula M6.PA.RelationalSource.language (^⊥ : M) := by simp
  have hleft : IsUFormula M6.PA.RelationalSource.language (relExtNegEq1 ^⋎ (relExtNegEq2 ^⋎ ^⊥) : M) := by
    simpa only [IsUFormula.or] using And.intro he1 (And.intro he2 hf)
  have htail : IsUFormula M6.PA.RelationalSource.language (relExtNegEq2 ^⋎ (^⊥ : M)) := by
    simpa only [IsUFormula.or] using And.intro he2 hf
  have hright : IsUFormula M6.PA.RelationalSource.language (eqRelExtNegOld ^⋎ eqRelExtPosNew : M) := by
    simpa only [IsUFormula.or] using And.intro hm1 hm2
  dsimp only
  rw [eqRelExtCore, reference_or params metadata _ _ _ hleft hright,
    reference_or params metadata _ _ _ he1 htail,
    reference_or params metadata _ _ _ he2 hf,
    reference_or params metadata _ _ _ hm1 hm2,
    reference_falsum, relExtNegEq1, relExtNegEq2, eqRelExtNegOld, eqRelExtPosNew,
    reference_neg_eq, reference_neg_eq, reference_neg_eq, reference_pos_eq]
  simp only [termLabel_bound_nth]

theorem eqRelExt_reference_binders (params metadata b : M) :
    formulaReference params metadata eqRelExtRoot ((((b+1)+1)+1)+1) =
      allValue (labelValue ((((b+1)+1)+1)+1) metadata)
      (allValue (labelValue (((b+1)+1)+1) metadata)
      (allValue (labelValue ((b+1)+1) metadata)
      (allValue (labelValue (b+1) metadata)
        (formulaReference params metadata eqRelExtCore b)))) := by
  have h0 := eqRelExtCore_valid (M := M)
  have h1 : IsUFormula M6.PA.RelationalSource.language (^∀ (eqRelExtCore (M := M))) := by simpa only [IsUFormula.all] using h0
  have h2 : IsUFormula M6.PA.RelationalSource.language (^∀ (^∀ (eqRelExtCore (M := M)))) := by simpa only [IsUFormula.all] using h1
  have h3 : IsUFormula M6.PA.RelationalSource.language (^∀ (^∀ (^∀ (eqRelExtCore (M := M))))) := by simpa only [IsUFormula.all] using h2
  rw [eqRelExtRoot, reference_all params metadata _ _ h3,
      reference_all params metadata _ _ h2,
      reference_all params metadata _ _ h1,
      reference_all params metadata _ _ h0]

theorem eqRelExt_reference_complete (b base reserve initial free : M) :
    let ceiling := ((((b+1)+1)+1)+1)
    let params := pair initial free
    let metadata := pair ceiling (pair base reserve)
    let x₀ := base
    let x₁ := base+1
    let x₂ := (base+1)+1
    let x₃ := ((base+1)+1)+1
    let e₁ := neighborhoodValue x₃ x₁ reserve
    let e₂ := neighborhoodValue x₂ x₀ reserve
    let old := neighborhoodValue x₃ x₂ reserve
    let new := neighborhoodValue x₁ x₀ reserve
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    formulaReference params metadata eqRelExtRoot ceiling =
      allValue x₀ (allValue x₁ (allValue x₂ (allValue x₃
        (impValue antecedent (impValue (negValue (negValue old)) new))))) := by
  dsimp only
  let ceiling := ((((b+1)+1)+1)+1)
  let metadata := pair ceiling (pair base reserve)
  have h0 : labelValue ceiling metadata = base := by
    simpa only [metadata, add_zero] using labelValue_add ceiling 0 base reserve
  have h1 : labelValue (((b+1)+1)+1) metadata = base+1 := by
    simpa only [metadata, ceiling] using labelValue_add (((b+1)+1)+1) 1 base reserve
  have h2 : labelValue ((b+1)+1) metadata = (base+1)+1 := by
    simpa only [metadata, ceiling, add_assoc] using labelValue_add ((b+1)+1) (1+1) base reserve
  have h3 : labelValue (b+1) metadata = ((base+1)+1)+1 := by
    simpa only [metadata, ceiling, add_assoc] using labelValue_add (b+1) ((1+1)+1) base reserve
  have hs := relExt_four_stack b base reserve initial free
  dsimp only at hs
  obtain ⟨hs0,hs1,hs2,hs3⟩ := hs
  rw [eqRelExt_reference_binders,eqRelExt_reference_core]
  simp only [pi₂_pair]
  change allValue (labelValue ceiling metadata) _ = _
  rw [h0,h1,h2,h3,hs0,hs1,hs2,hs3]

theorem eqRelExtRoot_four_le : (((((0 : M)+1)+1)+1)+1) ≤ eqRelExtRoot := by
  have ha (p : M) : p+1 ≤ ^∀ p := by
    change p+1 ≤ pair (6 : M) p+1
    simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) p) 1
  have hz : (0 : M) ≤ (eqRelExtCore (M := M)) := zero_le
  have h0 : (0 : M)+1 ≤ ^∀ (eqRelExtCore (M := M)) :=
    le_trans (by simpa only [add_comm] using add_le_add_right hz 1) (ha _)
  have h1 : ((0 : M)+1)+1 ≤ ^∀ (^∀ (eqRelExtCore (M := M))) :=
    le_trans (by simpa only [add_comm] using add_le_add_right h0 1) (ha _)
  have h2 : (((0 : M)+1)+1)+1 ≤ ^∀ (^∀ (^∀ (eqRelExtCore (M := M)))) :=
    le_trans (by simpa only [add_comm] using add_le_add_right h1 1) (ha _)
  simpa only [eqRelExtRoot] using le_trans (by simpa only [add_comm] using add_le_add_right h2 1) (ha _)

theorem eqRelExtRoot_budget_shape : ∃ b : M, eqRelExtRoot = ((((b+1)+1)+1)+1) := by
  obtain ⟨b,hb⟩ := le_iff_exists_add.mp (eqRelExtRoot_four_le (M := M))
  refine ⟨b,?_⟩
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using hb

theorem fixedFormulaTranslation_eqRelExt_target (initial free base reserve : M) :
    TargetProvable (F fixedFormulaTranslation ![(⌜sourceEqRelExt⌝ : M),initial,free,base,reserve]) := by
  rw [eqRelExtRoot_quote]
  rw [fixedFormulaTranslation_correct _ _ _ _ _ eqRelExtRoot_valid]
  obtain ⟨b,hb⟩ := eqRelExtRoot_budget_shape (M := M)
  have h := eqRelExt_reference_complete b base reserve initial free
  dsimp only at h
  rw [←hb] at h
  rw [h]
  exact equalityRelExtNNF_supplier base reserve

#print axioms fixedFormulaTranslation_eqRelExt_target
#print axioms eqRelExt_reference_complete
#print axioms eqRelExtRoot_four_le
#print axioms eqRelExtRoot_budget_shape
#print axioms eqRelExt_reference_core
#print axioms eqRelExtRoot_quote
#print axioms eqRelExtRoot_valid
end models
end PA194ModelLogic
