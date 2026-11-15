import PA194ModelRelExtSource
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
local instance relExtReferenceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance relExtReferenceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance relExtReferenceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance relExtReferenceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance relExtReferenceLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance relExtReferenceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reference_all (params metadata p b : M) (hp : IsUFormula M6.PA.RelationalSource.language p) :
    formulaReference params metadata (^∀ p) (b+1) =
      allValue (labelValue (b+1) metadata) (formulaReference params metadata p b) :=
  (formulaReference_recurrence params metadata).allRule p b hp

theorem reference_or (params metadata p q b : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    formulaReference params metadata (p ^⋎ q) b =
      impValue (negValue (formulaReference params metadata p b))
        (formulaReference params metadata q b) :=
  (formulaReference_recurrence params metadata).orRule p q b hp hq

theorem reference_falsum (params metadata b : M) :
    formulaReference params metadata (^⊥) b = memValue 0 0 :=
  (formulaReference_recurrence params metadata).falsum b

theorem reference_neg_eq (params metadata b a c : M) :
    formulaReference params metadata (^nrel (2 : M) 0 (relExtVector a c)) b =
      negValue (neighborhoodValue
        (F termLabelCode ![^#a,boundValue b params metadata,π₂ params])
        (F termLabelCode ![^#c,boundValue b params metadata,π₂ params])
        (π₂ (π₂ metadata))) := by
  have h := (formulaReference_recurrence params metadata).negative 0 (relExtVector a c) b
    relExt_relation_zero (relExt_vector_valid a c)
  change formulaReference params metadata (^nrel (2 : M) 0 (relExtVector a c)) b = _ at h
  rw [h]
  simp only [atomValue, ite_true]
  simpa only [negativeEqualityAtomCode, machineNeg_model, relExtVector, qqNRel] using
    negativeEqualityAtom_model (^#a) (^#c) (boundValue b params metadata) (π₂ params) (π₂ (π₂ metadata))

theorem reference_neg_mem (params metadata b a c : M) :
    formulaReference params metadata (^nrel (2 : M) 1 (relExtVector a c)) b =
      negValue (memValue
        (F termLabelCode ![^#c,boundValue b params metadata,π₂ params])
        (F termLabelCode ![^#a,boundValue b params metadata,π₂ params])) := by
  have h := (formulaReference_recurrence params metadata).negative 1 (relExtVector a c) b
    relExt_relation_one (relExt_vector_valid a c)
  change formulaReference params metadata (^nrel (2 : M) 1 (relExtVector a c)) b = _ at h
  rw [h]
  simp only [atomValue, Arithmetic.one_ne_zero, if_false]
  simpa only [negativeMembershipAtomCode, machineNeg_model, relExtVector, qqNRel] using
    negativeMembershipAtom_model (^#a) (^#c) (boundValue b params metadata) (π₂ params) (π₂ (π₂ metadata))

theorem reference_pos_mem (params metadata b a c : M) :
    formulaReference params metadata (^rel (2 : M) 1 (relExtVector a c)) b =
      memValue (F termLabelCode ![^#c,boundValue b params metadata,π₂ params])
        (F termLabelCode ![^#a,boundValue b params metadata,π₂ params]) := by
  have h := (formulaReference_recurrence params metadata).positive 1 (relExtVector a c) b
    relExt_relation_one (relExt_vector_valid a c)
  change formulaReference params metadata (^rel (2 : M) 1 (relExtVector a c)) b = _ at h
  rw [h]
  simp only [atomValue, Arithmetic.one_ne_zero, if_false]
  change F membershipAtomCode ![^rel (2 : M) 1 (relExtVector a c),_,_,_] = _
  exact membershipAtom_model (^#a) (^#c) _ _ _

theorem relExt_reference_core (params metadata b : M) :
    let bound := boundValue b params metadata
    let z := π₂ (π₂ metadata)
    let e₁ := neighborhoodValue bound.[0] bound.[2] z
    let e₂ := neighborhoodValue bound.[1] bound.[3] z
    let old := memValue bound.[1] bound.[0]
    let new := memValue bound.[3] bound.[2]
    formulaReference params metadata relExtCore b =
      impValue (negValue (impValue (negValue (negValue e₁))
        (impValue (negValue (negValue e₂)) (memValue 0 0))))
        (impValue (negValue (negValue old)) new) := by
  have he1 : IsUFormula M6.PA.RelationalSource.language (relExtNegEq1 (M := M)) := by
    simp only [relExtNegEq1,IsUFormula.nrel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 0 2⟩
  have he2 : IsUFormula M6.PA.RelationalSource.language (relExtNegEq2 (M := M)) := by
    simp only [relExtNegEq2,IsUFormula.nrel]
    exact ⟨relExt_relation_zero,relExt_vector_valid 1 3⟩
  have hm1 : IsUFormula M6.PA.RelationalSource.language (relExtNegMem (M := M)) := by
    simp only [relExtNegMem,IsUFormula.nrel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 1⟩
  have hm2 : IsUFormula M6.PA.RelationalSource.language (relExtPosMem (M := M)) := by
    simp only [relExtPosMem,IsUFormula.rel]
    exact ⟨relExt_relation_one,relExt_vector_valid 2 3⟩
  have hf : IsUFormula M6.PA.RelationalSource.language (^⊥ : M) := by simp
  have hleft : IsUFormula M6.PA.RelationalSource.language (relExtNegEq1 ^⋎ (relExtNegEq2 ^⋎ ^⊥) : M) := by
    simpa only [IsUFormula.or] using And.intro he1 (And.intro he2 hf)
  have htail : IsUFormula M6.PA.RelationalSource.language (relExtNegEq2 ^⋎ (^⊥ : M)) := by
    simpa only [IsUFormula.or] using And.intro he2 hf
  have hright : IsUFormula M6.PA.RelationalSource.language (relExtNegMem ^⋎ relExtPosMem : M) := by
    simpa only [IsUFormula.or] using And.intro hm1 hm2
  dsimp only
  rw [relExtCore, reference_or params metadata _ _ _ hleft hright,
    reference_or params metadata _ _ _ he1 htail,
    reference_or params metadata _ _ _ he2 hf,
    reference_or params metadata _ _ _ hm1 hm2,
    reference_falsum, relExtNegEq1, relExtNegEq2, relExtNegMem, relExtPosMem,
    reference_neg_eq, reference_neg_eq, reference_neg_mem, reference_pos_mem]
  simp only [termLabel_bound_nth]

theorem relExt_reference_binders (params metadata b : M) :
    formulaReference params metadata relExtRoot ((((b+1)+1)+1)+1) =
      allValue (labelValue ((((b+1)+1)+1)+1) metadata)
      (allValue (labelValue (((b+1)+1)+1) metadata)
      (allValue (labelValue ((b+1)+1) metadata)
      (allValue (labelValue (b+1) metadata)
        (formulaReference params metadata relExtCore b)))) := by
  have h0 := relExtCore_valid (M := M)
  have h1 : IsUFormula M6.PA.RelationalSource.language (^∀ (relExtCore (M := M))) := by simpa only [IsUFormula.all] using h0
  have h2 : IsUFormula M6.PA.RelationalSource.language (^∀ (^∀ (relExtCore (M := M)))) := by simpa only [IsUFormula.all] using h1
  have h3 : IsUFormula M6.PA.RelationalSource.language (^∀ (^∀ (^∀ (relExtCore (M := M))))) := by simpa only [IsUFormula.all] using h2
  rw [relExtRoot, reference_all params metadata _ _ h3,
      reference_all params metadata _ _ h2,
      reference_all params metadata _ _ h1,
      reference_all params metadata _ _ h0]

theorem labelValue_add (budget d base reserve : M) :
    labelValue budget (pair (budget+d) (pair base reserve)) = base+d := by
  simp only [labelValue,pi₁_pair,pi₂_pair,labelAtBudget_model]
  have h := modelSubAdd budget d
  change F subCode ![budget+d,budget] = d at h
  rw [h]

theorem boundValue_add (budget d base reserve initial free : M) :
    boundValue budget (pair initial free) (pair (budget+d) (pair base reserve)) =
      F allocateBound ![d,base,initial] := by
  simp only [boundValue,pi₁_pair,pi₂_pair,boundAtBudget_model]
  have h := modelSubAdd budget d
  change F subCode ![budget+d,budget] = d at h
  rw [h]

theorem relExt_four_stack (b base reserve initial free : M) :
    let ceiling := ((((b+1)+1)+1)+1)
    let bound := boundValue b (pair initial free) (pair ceiling (pair base reserve))
    bound.[0] = ((base+1)+1)+1 ∧ bound.[1] = (base+1)+1 ∧
      bound.[2] = base+1 ∧ bound.[3] = base := by
  have he : ((((b+1)+1)+1)+1) = b + ((((0+1)+1)+1)+1) := by simp [add_assoc]
  dsimp only
  rw [he,boundValue_add]
  simp only [allocateBound_succ,allocateBound_zero,add_zero,←adjoin_def]
  simp [show (3 : M) = 2+1 by norm_num, add_assoc]

theorem relExt_reference_complete (b base reserve initial free : M) :
    let ceiling := ((((b+1)+1)+1)+1)
    let params := pair initial free
    let metadata := pair ceiling (pair base reserve)
    let x₀ := base
    let x₁ := base+1
    let x₂ := (base+1)+1
    let x₃ := ((base+1)+1)+1
    let e₁ := neighborhoodValue x₃ x₁ reserve
    let e₂ := neighborhoodValue x₂ x₀ reserve
    let old := memValue x₂ x₃
    let new := memValue x₀ x₁
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    formulaReference params metadata relExtRoot ceiling =
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
  rw [relExt_reference_binders,relExt_reference_core]
  simp only [pi₂_pair]
  change allValue (labelValue ceiling metadata) _ = _
  rw [h0,h1,h2,h3,hs0,hs1,hs2,hs3]

theorem relExtRoot_four_le : (((((0 : M)+1)+1)+1)+1) ≤ relExtRoot := by
  have ha (p : M) : p+1 ≤ ^∀ p := by
    change p+1 ≤ pair (6 : M) p+1
    simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) p) 1
  have hz : (0 : M) ≤ (relExtCore (M := M)) := zero_le
  have h0 : (0 : M)+1 ≤ ^∀ (relExtCore (M := M)) :=
    le_trans (by simpa only [add_comm] using add_le_add_right hz 1) (ha _)
  have h1 : ((0 : M)+1)+1 ≤ ^∀ (^∀ (relExtCore (M := M))) :=
    le_trans (by simpa only [add_comm] using add_le_add_right h0 1) (ha _)
  have h2 : (((0 : M)+1)+1)+1 ≤ ^∀ (^∀ (^∀ (relExtCore (M := M)))) :=
    le_trans (by simpa only [add_comm] using add_le_add_right h1 1) (ha _)
  simpa only [relExtRoot] using le_trans (by simpa only [add_comm] using add_le_add_right h2 1) (ha _)

theorem relExtRoot_budget_shape : ∃ b : M, relExtRoot = ((((b+1)+1)+1)+1) := by
  obtain ⟨b,hb⟩ := le_iff_exists_add.mp (relExtRoot_four_le (M := M))
  refine ⟨b,?_⟩
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using hb

theorem fixedFormulaTranslation_relExt_target
    (initial free base reserve : M) (hz : ((((base+1)+1)+1)+1) ≤ reserve) :
    TargetProvable (F fixedFormulaTranslation
      ![(⌜PA194RelExtTypedTranslation.sourceRelExt⌝ : M),initial,free,base,reserve]) := by
  rw [relExtRoot_quote]
  rw [fixedFormulaTranslation_correct _ _ _ _ _ relExtRoot_valid]
  obtain ⟨b,hb⟩ := relExtRoot_budget_shape (M := M)
  have h := relExt_reference_complete b base reserve initial free
  dsimp only at h
  rw [←hb] at h
  rw [h]
  exact relExtNNF_budget_supplier base reserve hz

#print axioms relExtRoot_four_le
#print axioms relExtRoot_budget_shape
#print axioms fixedFormulaTranslation_relExt_target
#print axioms relExt_reference_complete
#print axioms labelValue_add
#print axioms boundValue_add
#print axioms relExt_four_stack
#print axioms relExt_reference_core
#print axioms relExt_reference_binders
end models
end PA194ModelLogic
