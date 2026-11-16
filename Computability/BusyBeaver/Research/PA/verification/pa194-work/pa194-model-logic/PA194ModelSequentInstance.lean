import ConPASetSequent
import PA194ModelContext
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
local instance sequentInstanceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sequentInstanceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sequentInstanceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sequentInstanceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sequentInstanceLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sequentInstanceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Environment is pair(bound,pair(free,pair(base,reserve))). -/
noncomputable def sequentEnvBound : Code 2 := unary firstProjection (.proj 0)
noncomputable def sequentEnvTail : Code 2 := unary secondProjection (.proj 0)
noncomputable def sequentEnvFree : Code 2 := unary firstProjection sequentEnvTail
noncomputable def sequentEnvLabels : Code 2 := unary secondProjection sequentEnvTail
noncomputable def sequentEnvBase : Code 2 := unary firstProjection sequentEnvLabels
noncomputable def sequentEnvReserve : Code 2 := unary secondProjection sequentEnvLabels
noncomputable def sequentFormulaCode : Code 2 :=
  machineNeg (.comp fixedFormulaTranslation
    (.cons (.proj 1) (.cons sequentEnvBound (.cons sequentEnvFree
      (.cons sequentEnvBase (.cons sequentEnvReserve (.nil 2)))))))

noncomputable def sequentImpCode : Code 2 := machineImp (.proj 0) (.proj 1)
noncomputable def sequentAllCode : Code 2 := machineAll (.proj 0) (.proj 1)

theorem sequentImpCode_model (a b : M) : F sequentImpCode ![a,b] = impValue a b := by
  simp [sequentImpCode,machineImp_model,modelProjection]

theorem sequentAllCode_model (a b : M) : F sequentAllCode ![a,b] = allValue a b := by
  simp [sequentAllCode,machineAll_model,modelProjection]

noncomputable def numericalCalc : ConPA.Sequent.Calc M where
  imp := impValue
  impDef := PA194CodeGraph.graph sequentImpCode
  imp_defined := .mk fun v => by
    have h := (PA194CodeGraph.modelGraph (M := M) sequentImpCode).defined v
    have hv : (fun i : Fin 2 => v i.succ) = ![v 1,v 2] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    rw [hv] at h
    dsimp only at h
    rw [sequentImpCode_model] at h
    simpa using h
  Pr := TargetProvable
  pr_definable := targetProvable_definable
  mp := tp_mp
  k := imp_k
  s := imp_s
  comp := imp_comp
  exchange := imp_exchange

noncomputable def numericalQuant : ConPA.Sequent.Quant M where
  toCalc := numericalCalc
  all := allValue
  allDef := PA194CodeGraph.graph sequentAllCode
  all_defined := .mk fun v => by
    have h := (PA194CodeGraph.modelGraph (M := M) sequentAllCode).defined v
    have hv : (fun i : Fin 2 => v i.succ) = ![v 1,v 2] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    rw [hv] at h
    dsimp only at h
    rw [sequentAllCode_model] at h
    simpa using h
  gen := tp_gen
  dist := r2

noncomputable def negatedTranslation (e p : M) : M := F sequentFormulaCode ![e,p]

noncomputable def numericalTranslation : ConPA.Sequent.Tr M where
  tr := negatedTranslation
  trDef := PA194CodeGraph.graph sequentFormulaCode
  tr_defined := .mk fun v => by
    have h := (PA194CodeGraph.modelGraph (M := M) sequentFormulaCode).defined v
    have hv : (fun i : Fin 2 => v i.succ) = ![v 1,v 2] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    rw [hv] at h
    dsimp only at h
    simpa [negatedTranslation] using h

theorem negatedTranslation_model (bound free base reserve p : M) :
    negatedTranslation (pair bound (pair free (pair base reserve))) p =
      negValue (F fixedFormulaTranslation ![p,bound,free,base,reserve]) := by
  simp only [negatedTranslation,sequentFormulaCode,machineNeg_model,modelComposition]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change F (.proj 1 : Code 2) ![pair bound (pair free (pair base reserve)),p] = p
    simp [modelProjection]
  refine Fin.cases ?_ (fun k => ?_) j
  · change F sequentEnvBound ![pair bound (pair free (pair base reserve)),p] = bound
    simp [sequentEnvBound,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,pi₁_pair]
  refine Fin.cases ?_ (fun l => ?_) k
  · change F sequentEnvFree ![pair bound (pair free (pair base reserve)),p] = free
    simp [sequentEnvFree,sequentEnvTail,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,
      modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  refine Fin.cases ?_ (fun m => ?_) l
  · change F sequentEnvBase ![pair bound (pair free (pair base reserve)),p] = base
    simp [sequentEnvBase,sequentEnvLabels,sequentEnvTail,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,
      modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  refine Fin.cases ?_ (fun n => Fin.elim0 n) m
  · change F sequentEnvReserve ![pair bound (pair free (pair base reserve)),p] = reserve
    simp [sequentEnvReserve,sequentEnvLabels,sequentEnvTail,modelUnary,modelProjection,
      modelPi2Code secondProjection secondProjection_certified,pi₂_pair]

/-- A positive translated target theorem closes any internal finite source sequent
containing its source formula code, under the negated-translation convention. -/
theorem translatedAxiom_sseq (bound free base reserve p s : M)
    (hp : p ∈ s)
    (hprov : TargetProvable (F fixedFormulaTranslation ![p,bound,free,base,reserve])) :
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) s 1) := by
  let e := pair bound (pair free (pair base reserve))
  let A := F fixedFormulaTranslation ![p,bound,free,base,reserve]
  have hpos := ConPA.Sequent.sseq_weaken numericalCalc numericalTranslation hprov e s
  have hneg := ConPA.Sequent.sseq_mem numericalCalc numericalTranslation e hp
  change TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation e
    s (negatedTranslation e p)) at hneg
  rw [negatedTranslation_model] at hneg
  change TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation e
    s (impValue A 1)) at hneg
  exact ConPA.Sequent.sseq_mp numericalCalc numericalTranslation hpos hneg

#print axioms translatedAxiom_sseq
#print axioms numericalTranslation
#print axioms negatedTranslation_model
#print axioms numericalCalc
#print axioms numericalQuant
end models
end PA194ModelLogic
