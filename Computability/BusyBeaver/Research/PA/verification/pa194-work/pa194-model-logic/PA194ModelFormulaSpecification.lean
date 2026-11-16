import PA194ModelFormulaUniquenessF

/-! Independent Foundation UformulaRec1 specification of the source-to-numerical
translation, with explicit model-valued budget and fixed context. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- Inputs: parameter `pair budget (pair params metadata)` and a source atom. -/
noncomputable def specBudget : Code 2 := unary firstProjection (.proj 0)
noncomputable def specContext : Code 2 := unary secondProjection (.proj 0)
noncomputable def specParams : Code 2 := unary firstProjection specContext
noncomputable def specMetadata : Code 2 := unary secondProjection specContext
noncomputable def specIndex : Code 2 := bin pairCode (.proj 1) specBudget
noncomputable def specAtom : Code 2 :=
  applyFour positiveAtomResult specIndex (.zero 2) specParams specMetadata
noncomputable def specNegAtom : Code 2 := machineNeg specAtom
noncomputable def specAnd : Code 2 := machineConj (.proj 0) (.proj 1)
noncomputable def specOr : Code 2 := machineImp (machineNeg (.proj 0)) (.proj 1)
noncomputable def specFalsum : Code 0 := machineMem (.zero 0) (.zero 0)
noncomputable def specCeiling : Code 2 := unary firstProjection specMetadata
noncomputable def specBase : Code 2 := unary firstProjection (unary secondProjection specMetadata)
noncomputable def specLabel : Code 2 := PA194TargetStep.app3 labelAtBudget specBudget specCeiling specBase
noncomputable def specAll : Code 2 := machineAll specLabel (.proj 1)
noncomputable def specEx : Code 2 := machineEx specLabel (.proj 1)
noncomputable def specChange : Code 1 :=
  bin pairCode (unary predCode (unary firstProjection (.proj 0))) (unary secondProjection (.proj 0))

noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ a, !qqRelDef a k R v ∧ !(PA194CodeGraph.graph specAtom) y param a”
  nrel := .mkSigma “y param k R v. ∃ a, !qqNRelDef a k R v ∧ !(PA194CodeGraph.graph specNegAtom) y param a”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. !(PA194CodeGraph.graph specFalsum) y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !(PA194CodeGraph.graph specAnd) y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !(PA194CodeGraph.graph specOr) y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !(PA194CodeGraph.graph specAll) y param y₁”
  exs := .mkSigma “y param p₁ y₁. !(PA194CodeGraph.graph specEx) y param y₁”
  allChanges := .mkSigma “y param. !(PA194CodeGraph.graph specChange) y param”
  exsChanges := .mkSigma “y param. !(PA194CodeGraph.graph specChange) y param”

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

theorem graph_eval {n : Nat} (code : Code n) (v : Fin (n+1) → M) :
    (PA194CodeGraph.graph code).val.Evalb v ↔ v 0 = F code (fun i => v i.succ) :=
  (PA194CodeGraph.modelGraph (M := M) code).defined v

noncomputable def formulaConstruction : UformulaRec1.Construction M formulaBlueprint where
  rel p k R v := F specAtom ![p,^rel k R v]
  nrel p k R v := F specNegAtom ![p,^nrel k R v]
  verum _ := 0
  falsum _ := F specFalsum Fin.elim0
  and _ _ _ y₁ y₂ := F specAnd ![y₁,y₂]
  or _ _ _ y₁ y₂ := F specOr ![y₁,y₂]
  all p _ y := F specAll ![p,y]
  exs p _ y := F specEx ![p,y]
  allChanges p := F specChange ![p]
  exsChanges p := F specChange ![p]
  rel_defined := .mk fun v => by
    simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
  nrel_defined := .mk fun v => by
    simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
  verum_defined := .mk fun v => by simp [formulaBlueprint]
  falsum_defined := .mk fun v => by
    have he : (fun _ : Fin 0 => v 0) = Fin.elim0 := Subsingleton.elim _ _
    simp [formulaBlueprint,graph_eval,he]
  and_defined := .mk fun v => by simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons']
  or_defined := .mk fun v => by simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons']
  all_defined := .mk fun v => by simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons']
  exs_defined := .mk fun v => by simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons']
  allChanges_defined := .mk fun v => by
    have he : (fun _ : Fin 1 => v 1) = ![v 1] := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons',he]
  exChanges_defined := .mk fun v => by
    have he : (fun _ : Fin 1 => v 1) = ![v 1] := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    simp [formulaBlueprint,graph_eval,Matrix.comp_vecCons',he]

/-- Independent, Σ₁-defined structural recursion on internally valid source codes. -/
noncomputable def formulaReference (params metadata p b : M) : M :=
  (formulaConstruction (M := M)).result M6.PA.RelationalSource.language (pair b (pair params metadata)) p

theorem formulaReference_definable (params metadata : M) :
    𝚺₁-Function₂ (formulaReference params metadata : M → M → M) := by
  haveI : 𝚺₁-Function₂ ((formulaConstruction (M := M)).result M6.PA.RelationalSource.language) :=
    (formulaConstruction (M := M)).result_definable
  unfold formulaReference
  definability

theorem specAtom_model (atom b params metadata : M) :
    F specAtom ![pair b (pair params metadata),atom] =
      F positiveAtomResult ![pair atom b,0,params,metadata] := by
  simp only [specAtom,applyFour_model,specIndex,specBudget,specParams,specMetadata,specContext,
    modelBin,modelPairCode,modelUnary,modelProjection,PRAMultiplication.modelZero,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rfl

theorem specChange_model (b params metadata : M) :
    F specChange ![pair (b+1) (pair params metadata)] = pair b (pair params metadata) := by
  simp only [specChange,modelBin,modelPairCode,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair,
    Matrix.cons_val_zero,modelPredAddOne]

theorem specLabel_model (b params metadata child : M) :
    F specLabel ![pair b (pair params metadata),child] = labelValue b metadata := by
  simp only [specLabel,PA194TargetStep.app3_model,specBudget,specCeiling,specBase,specMetadata,specContext,
    modelUnary,modelProjection,modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair,
    Matrix.cons_val_zero,Matrix.vecHead,Function.comp_def,labelValue]

/-- The independent structural recursion satisfies the constructor specification
on internally valid source syntax. No freshness of the reserved label is assumed. -/
theorem formulaReference_recurrence (params metadata : M) :
    FormulaRecurrenceF (formulaReference params metadata) params metadata where
  positive := by
    intro r v b hr hv
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (^rel (2 : M) r v) = _
    rw [(formulaConstruction (M := M)).result_rel hr hv]
    change F specAtom ![pair b (pair params metadata),pair (0 : M) (pair 2 (pair r v))+1] = _
    rw [specAtom_model,positiveAtomResult_model,sourceRel_model,sourceRoot,modelSrc firstProjection firstProjection_certified]
    have hc := currentValues_any (pair (0 : M) (pair 2 (pair r v))+1) b 0 params metadata
    dsimp only at hc
    rw [hc.1,hc.2.2.1,hc.2.2.2]
    rfl
  negative := by
    intro r v b hr hv
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (^nrel (2 : M) r v) = _
    rw [(formulaConstruction (M := M)).result_nrel hr hv]
    change F specNegAtom ![pair b (pair params metadata),pair (1 : M) (pair 2 (pair r v))+1] = _
    rw [specNegAtom,machineNeg_model,specAtom_model,positiveAtomResult_model,sourceRel_model,
      sourceRoot,modelSrc firstProjection firstProjection_certified]
    have hc := currentValues_any (pair (1 : M) (pair 2 (pair r v))+1) b 0 params metadata
    dsimp only at hc
    rw [hc.1,hc.2.2.1,hc.2.2.2]
    rfl
  truth := by
    intro b
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (^⊤) = _
    rw [(formulaConstruction (M := M)).result_verum]
    rfl
  falsum := by
    intro b
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (^⊥) = _
    rw [(formulaConstruction (M := M)).result_falsum]
    change F specFalsum Fin.elim0 = _
    rw [specFalsum,mem_model,PRAMultiplication.modelZero]
    rfl
  andRule := by
    intro p q b hp hq
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (p ^⋏ q) = _
    rw [(formulaConstruction (M := M)).result_and hp hq]
    change F specAnd ![_,_] = _
    simp only [specAnd,conj_model,machineImp_model,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  orRule := by
    intro p q b hp hq
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair b (pair params metadata)) (p ^⋎ q) = _
    rw [(formulaConstruction (M := M)).result_or hp hq]
    change F specOr ![_,_] = _
    simp only [specOr,machineImp_model,machineNeg_model,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  allRule := by
    intro p b hp
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair (b+1) (pair params metadata)) (^∀ p) = _
    rw [(formulaConstruction (M := M)).result_all hp]
    change F specAll ![pair (b+1) (pair params metadata),
      (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
        (F specChange ![pair (b+1) (pair params metadata)]) p] = _
    rw [specAll,machineAll_model,specLabel_model,modelProjection,specChange_model]
    rfl
  exRule := by
    intro p b hp
    change (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
      (pair (b+1) (pair params metadata)) (^∃ p) = _
    rw [(formulaConstruction (M := M)).result_exs hp]
    change F specEx ![pair (b+1) (pair params metadata),
      (formulaConstruction (M := M)).result M6.PA.RelationalSource.language
        (F specChange ![pair (b+1) (pair params metadata)]) p] = _
    rw [specEx,machineEx_model,specLabel_model,modelProjection,specChange_model]
    rfl

/-- The finite packed history agrees with the independent Foundation Σ₁
structural recursion for every internally valid (possibly nonstandard) source formula,
provided the remaining budget bounds the source code. This is a syntactic equation;
no freshness or semantic interpretation is asserted. -/
theorem formulaHistory_reference (p b params metadata : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) (hbudget : p ≤ b) :
    F formulaHistory ![p,b,params,metadata] = formulaReference params metadata p b :=
  boundedAgreementF_of_recurrence (formulaReference params metadata) b params metadata
    (formulaReference_definable params metadata) (formulaReference_recurrence params metadata)
    p hp b (le_refl b) hbudget

/-- In particular, the conservative root budget `p` needs no extra bound hypothesis. -/
theorem formulaHistory_reference_root (p params metadata : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F formulaHistory ![p,p,params,metadata] = formulaReference params metadata p p :=
  formulaHistory_reference p p params metadata hp (le_refl p)

#print axioms formulaHistory_reference
#print axioms formulaHistory_reference_root
#print axioms formulaReference_recurrence
#print axioms formulaReference_definable
#print axioms specAtom_model
#print axioms specChange_model
#print axioms specLabel_model
#print axioms graph_eval
#print axioms formulaConstruction
end models
#print axioms formulaBlueprint
end PA194ModelLogic
