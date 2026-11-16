import PA194FormulaFreeBound
import PA194UniformClose
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- One plus the free index of a source term, or zero for a bound term. -/
noncomputable def pureTermFreeBound (t : V) : V :=
  if t = 0 then 0 else if pi₁ (t-1) = 1 then pi₂ (t-1)+1 else 0

theorem pureTermFreeBoundGraph_iff (y t : V) :
    termFreeBoundGraph.val.Eval ![y,t] Empty.elim ↔ y = pureTermFreeBound t := by
  simp only [termFreeBoundGraph]
  simp
  rcases zero_or_succ t with rfl | ⟨d,rfl⟩
  · simp [pureTermFreeBound]
  · have hpair : pair (pi₁ d) (pi₂ d) = d := by
      simpa only [pi₁,pi₂] using pair_unpair d
    simp only [pureTermFreeBound,add_ne_zero,Arithmetic.one_ne_zero,or_true,ite_false,add_tsub_cancel_right]
    constructor
    · rintro (h0 | ⟨r,a,ht,hcases⟩)
      · simp at h0
      · have hd : d = pair r a := add_right_cancel ht
        subst d
        simp only [pi₁_pair,pi₂_pair]
        rcases hcases with ⟨hr,hy⟩ | ⟨hr,hy⟩
        · simp [hr,hy]
        · simp [hr,hy]
    · intro hy
      right
      refine ⟨pi₁ d, pi₂ d, ?_, ?_⟩
      · simpa [hpair]
      · by_cases h : pi₁ d = 1
        · left; exact ⟨h, by simpa [h] using hy⟩
        · right; exact ⟨h, by simpa [h] using hy⟩

theorem pureTermFreeBound_bvar (z : V) : pureTermFreeBound (^#z) = 0 := by simp [pureTermFreeBound,qqBvar]
theorem pureTermFreeBound_fvar (x : V) : pureTermFreeBound (^&x) = x+1 := by simp [pureTermFreeBound,qqFvar]

local instance pureTermFreeBound_defined : 𝚺₁-Function₁ (pureTermFreeBound : V → V) via termFreeBoundGraph := .mk fun v ↦ by
  change termFreeBoundGraph.val.Eval v Empty.elim ↔ v 0 = pureTermFreeBound (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using pureTermFreeBoundGraph_iff (v 0) (v 1)

/-- Largest free index plus one in the two arguments of a source relation. -/
noncomputable def purePairFreeBound (v : V) : V := max (pureTermFreeBound v.[0]) (pureTermFreeBound v.[1])

local instance purePairFreeBound_defined : 𝚺₁-Function₁ (purePairFreeBound : V → V) via pairFreeBoundGraph := .mk fun v ↦ by
  simp [pairFreeBoundGraph,purePairFreeBound]

noncomputable def pureFormulaFreeConstruction : UformulaRec1.Construction V FormulaFreeBound.blueprint where
  rel := fun _ _ _ v ↦ purePairFreeBound v
  nrel := fun _ _ _ v ↦ purePairFreeBound v
  verum := fun _ ↦ 0
  falsum := fun _ ↦ 0
  and := fun _ _ _ y₁ y₂ ↦ max y₁ y₂
  or := fun _ _ _ y₁ y₂ ↦ max y₁ y₂
  all := fun _ _ y₁ ↦ y₁
  exs := fun _ _ y₁ ↦ y₁
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  nrel_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  verum_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  falsum_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  and_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  or_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  all_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  exs_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  allChanges_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]
  exChanges_defined := .mk fun v ↦ by simp [FormulaFreeBound.blueprint]

noncomputable def pureFormulaFreeBound (p : V) : V := pureFormulaFreeConstruction.result SourceL 0 p


noncomputable def pureFormulaFreeBoundGraph : 𝚺₁.Semisentence 2 :=
  (FormulaFreeBound.blueprint.result SourceL).rew (Rew.subst ![#0, ‘0’, #1])

theorem pureFormulaFreeBound_defined : 𝚺₁-Function₁ (pureFormulaFreeBound : V → V) via pureFormulaFreeBoundGraph := .mk fun v => by
  simp [pureFormulaFreeBoundGraph,pureFormulaFreeBound,
    pureFormulaFreeConstruction.result_defined.defined]
#print axioms pureFormulaFreeBound_defined
end generic
end PA194BindSource
