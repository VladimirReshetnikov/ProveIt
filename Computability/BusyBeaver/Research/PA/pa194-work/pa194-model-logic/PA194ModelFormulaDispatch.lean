import PA194ModelMembershipAtomCode
import PA194SourceShiftHistory

/-! Candidate-PRA dispatcher for source-to-numerical formulas. Boolean children
retain the same budget; quantified bodies use one less budget. The dispatcher
is not, by itself, a structural-induction correctness proof. -/
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
 PA194FormulaUpdate PA194ParamHistory PA194TermRecursion PA194CloseFunction PA194VariableDispatch PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

noncomputable def sourceTag : Code 4 := PA194FormulaUpdate.tag firstProjection
noncomputable def sourceRoot : Code 4 := PA194FormulaUpdate.src firstProjection
noncomputable def sourceRel : Code 4 :=
  PA194FormulaUpdate.apply4 firstProjection (PA194FormulaUpdate.right firstProjection secondProjection)
noncomputable def positiveAtomResult : Code 4 :=
  let eq := applyFour equalityAtomCode sourceRoot currentBound freeEnvironment reservedLabel
  let mem := applyFour membershipAtomCode sourceRoot currentBound freeEnvironment reservedLabel
  selectAmong (bin equalityCode sourceRel (numeralCode 4 0)) eq mem
noncomputable def negativeAtomResult : Code 4 := machineNeg positiveAtomResult
noncomputable def leftResult : Code 4 :=
  PA194FormulaUpdate.childAt firstProjection secondProjection
    (PA194FormulaUpdate.left firstProjection secondProjection) remainingBudget
noncomputable def rightResult : Code 4 :=
  PA194FormulaUpdate.childAt firstProjection secondProjection
    (PA194FormulaUpdate.right firstProjection secondProjection) remainingBudget
noncomputable def bodyResult : Code 4 :=
  PA194FormulaUpdate.childAt firstProjection secondProjection
    (PA194FormulaUpdate.payload firstProjection secondProjection)
    (bin subCode remainingBudget (numeralCode 4 1))
noncomputable def andResult : Code 4 := machineConj leftResult rightResult
noncomputable def orResult : Code 4 := machineImp (machineNeg leftResult) rightResult
noncomputable def allResult : Code 4 := machineAll currentLabel bodyResult
noncomputable def exResult : Code 4 := machineEx currentLabel bodyResult
noncomputable def formulaNext : Code 4 :=
  let test (n : Nat) := bin equalityCode sourceTag (numeralCode 4 n)
  selectAmong (test 0) positiveAtomResult
    (selectAmong (test 1) negativeAtomResult
      (selectAmong (test 2) (.zero 4)
        (selectAmong (test 3) (machineMem (.zero 4) (.zero 4))
          (selectAmong (test 4) andResult
            (selectAmong (test 5) orResult
              (selectAmong (test 6) allResult exResult))))))
noncomputable def formulaHistory : Code 4 := PA194FormulaBudget.packedResult formulaNext

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

theorem formulaNext_model (e : Fin 4 → M) :
    F formulaNext e =
      if F sourceTag e = 0 then F positiveAtomResult e
      else if F sourceTag e = 1 then F negativeAtomResult e
      else if F sourceTag e = 2 then F (.zero 4) e
      else if F sourceTag e = 3 then F (machineMem (.zero 4) (.zero 4)) e
      else if F sourceTag e = 4 then F andResult e
      else if F sourceTag e = 5 then F orResult e
      else if F sourceTag e = 6 then F allResult e
      else F exResult e := by
  simp only [formulaNext,modelChooseEqual,modelNumeralCode]
  norm_num

/-- Conjunction children are evaluated at the same remaining budget. -/
theorem formulaHistory_and (p q b params metadata : M) :
    F formulaHistory ![pair (4 : M) (pair p q)+1,b,params,metadata] =
      conjValue (F formulaHistory ![p,b,params,metadata]) (F formulaHistory ![q,b,params,metadata]) := by
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [andResult,PA194TargetGate.conj_model,leftResult,rightResult,modelChildAt,modelChildAt,
    modelLeft firstProjection secondProjection firstProjection_certified secondProjection_certified,
    modelRight firstProjection secondProjection firstProjection_certified secondProjection_certified,
    remainingBudget,modelBudget secondProjection secondProjection_certified]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hp : p < pair (4 : M) (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
  have hq : q < pair (4 : M) (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
  rw [PA194FormulaBudget.lookup_same formulaNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified p (pair (4 : M) (pair p q)+1) b params metadata hp,
    PA194FormulaBudget.lookup_same formulaNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified q (pair (4 : M) (pair p q)+1) b params metadata hq]

/-- Disjunction children are evaluated at the same remaining budget. -/
theorem formulaHistory_or (p q b params metadata : M) :
    F formulaHistory ![pair (5 : M) (pair p q)+1,b,params,metadata] =
      impValue (negValue (F formulaHistory ![p,b,params,metadata])) (F formulaHistory ![q,b,params,metadata]) := by
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [orResult,machineImp_model,machineNeg_model,leftResult,rightResult,modelChildAt,modelChildAt,
    modelLeft firstProjection secondProjection firstProjection_certified secondProjection_certified,
    modelRight firstProjection secondProjection firstProjection_certified secondProjection_certified,
    remainingBudget,modelBudget secondProjection secondProjection_certified]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hp : p < pair (5 : M) (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
  have hq : q < pair (5 : M) (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
  rw [PA194FormulaBudget.lookup_same formulaNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified p (pair (5 : M) (pair p q)+1) b params metadata hp,
    PA194FormulaBudget.lookup_same formulaNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified q (pair (5 : M) (pair p q)+1) b params metadata hq]

/-- Universal bodies are evaluated at one less remaining budget. -/
theorem formulaHistory_all (p b params metadata : M) :
    let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair (pair (6 : M) p+1) (b+1),params,metadata]
    let e := ![pair (pair (6 : M) p+1) (b+1),hist,params,metadata]
    F formulaHistory ![pair (6 : M) p+1,b+1,params,metadata] =
      allValue (F currentLabel e) (F formulaHistory ![p,b,params,metadata]) := by
  dsimp only
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [allResult,machineAll_model,bodyResult,modelChildAt,
    modelPayload firstProjection secondProjection firstProjection_certified secondProjection_certified,
    modelBin,remainingBudget,modelBudget secondProjection secondProjection_certified,modelNumeralCode]
  norm_num
  have hsub : F subCode ![b+1,1] = b := by
    have h := modelSubAdd (M := M) 1 b
    change F subCode ![1+b,1] = b at h
    simpa [add_comm] using h
  rw [hsub]
  rw [PA194FormulaBudget.lookup_binder formulaNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified p (pair (6 : M) p+1) b params metadata]
  exact lt_of_le_of_lt (le_pair_right (6 : M) p) (lt_add_one _)

/-- Existential bodies are evaluated at one less remaining budget. -/
theorem formulaHistory_exs (p b params metadata : M) :
    let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair (pair (7 : M) p+1) (b+1),params,metadata]
    let e := ![pair (pair (7 : M) p+1) (b+1),hist,params,metadata]
    F formulaHistory ![pair (7 : M) p+1,b+1,params,metadata] =
      exValue (F currentLabel e) (F formulaHistory ![p,b,params,metadata]) := by
  dsimp only
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [exResult,machineEx_model,bodyResult,modelChildAt,
    modelPayload firstProjection secondProjection firstProjection_certified secondProjection_certified,
    modelBin,remainingBudget,modelBudget secondProjection secondProjection_certified,modelNumeralCode]
  norm_num
  have hsub : F subCode ![b+1,1] = b := by
    have h := modelSubAdd (M := M) 1 b
    change F subCode ![1+b,1] = b at h
    simpa [add_comm] using h
  rw [hsub]
  rw [PA194FormulaBudget.lookup_binder formulaNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified p (pair (7 : M) p+1) b params metadata]
  exact lt_of_le_of_lt (le_pair_right (7 : M) p) (lt_add_one _)

/-- Truth and falsity ignore the history and preserve the current budget. -/
theorem formulaHistory_truth (payload b params metadata : M) :
    F formulaHistory ![pair (2 : M) payload+1,b,params,metadata] = 0 := by
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  exact PRAMultiplication.modelZero _

theorem formulaHistory_falsum (payload b params metadata : M) :
    F formulaHistory ![pair (3 : M) payload+1,b,params,metadata] = memValue 0 0 := by
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [mem_model,PRAMultiplication.modelZero]
  rfl

theorem sourceRel_model (tag relation vector b hist params metadata : M) :
    F sourceRel ![pair (pair tag (pair 2 (pair relation vector))+1) b,hist,params,metadata] = relation := by
  rw [sourceRel,modelApply4,
    modelRight firstProjection secondProjection firstProjection_certified secondProjection_certified,
    modelPi1Code firstProjection firstProjection_certified,pi₁_pair]

theorem positiveAtomResult_model (e : Fin 4 → M) :
    F positiveAtomResult e =
      if F sourceRel e = 0 then F equalityAtomCode ![F sourceRoot e,F currentBound e,F freeEnvironment e,F reservedLabel e]
      else F membershipAtomCode ![F sourceRoot e,F currentBound e,F freeEnvironment e,F reservedLabel e] := by
  simp only [positiveAtomResult,modelChooseEqual,modelNumeralCode,applyFour_model]
  norm_num

theorem formulaHistory_positiveAtom (relation vector b params metadata : M) :
    let atom := pair (0 : M) (pair 2 (pair relation vector))+1
    let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair atom b,params,metadata]
    let e := ![pair atom b,hist,params,metadata]
    F formulaHistory ![atom,b,params,metadata] =
      if relation = 0 then F equalityAtomCode ![atom,F currentBound e,F freeEnvironment e,F reservedLabel e]
      else F membershipAtomCode ![atom,F currentBound e,F freeEnvironment e,F reservedLabel e] := by
  dsimp only
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [positiveAtomResult_model,sourceRel_model,sourceRoot,modelSrc firstProjection firstProjection_certified]

theorem formulaHistory_negativeAtom (relation vector b params metadata : M) :
    let atom := pair (1 : M) (pair 2 (pair relation vector))+1
    let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair atom b,params,metadata]
    let e := ![pair atom b,hist,params,metadata]
    F formulaHistory ![atom,b,params,metadata] =
      negValue (if relation = 0 then F equalityAtomCode ![atom,F currentBound e,F freeEnvironment e,F reservedLabel e]
        else F membershipAtomCode ![atom,F currentBound e,F freeEnvironment e,F reservedLabel e]) := by
  dsimp only
  rw [formulaHistory,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,
    formulaNext_model,sourceTag,modelTag firstProjection firstProjection_certified]
  norm_num
  rw [negativeAtomResult,machineNeg_model,positiveAtomResult_model,sourceRel_model,sourceRoot,modelSrc firstProjection firstProjection_certified]

#print axioms formulaHistory_negativeAtom
#print axioms sourceRel_model
#print axioms positiveAtomResult_model
#print axioms formulaHistory_positiveAtom
#print axioms formulaHistory_truth
#print axioms formulaHistory_falsum
#print axioms formulaHistory_exs
#print axioms formulaHistory_all
#print axioms formulaHistory_or
#print axioms formulaHistory_and
#print axioms formulaNext_model
end models
end PA194ModelLogic
