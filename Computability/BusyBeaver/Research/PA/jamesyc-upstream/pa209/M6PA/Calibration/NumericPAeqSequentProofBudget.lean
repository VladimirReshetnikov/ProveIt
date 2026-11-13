module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentDerivationInvariant
public import M6PA.Calibration.NumericPAeqSequentEigenShift
@[expose] public section

/-! Proof-wide source support is derived from the actual derivation code,
not inferred from support of its end sequent. No derivation induction is
claimed here. The target term environment and its domain guard are unchanged. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def SourceProofBudget (d f : V) : Prop :=
  IsSemitermVec language (len f) 0 f ∧ d≤len f

noncomputable def sourceProofBudgetGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “d f. ∃ n, !lenDef n f ∧ !((isSemitermVec language).sigma) n 0 f ∧ d≤n”

theorem sourceProofBudget_graph (d f : V) :
    sourceProofBudgetGraph.val.Evalb ![d,f] ↔ SourceProofBudget d f := by
  simp [sourceProofBudgetGraph,SourceProofBudget,Matrix.comp_vecCons'']

theorem ordinary_derivation_positive {d : V}
    (h : Derivation Presentation.ordinaryPAeq d) : 0<d := by
  rcases Derivation.case_iff.mp h with ⟨hs,hcases⟩
  rcases hcases with ⟨s,p,rfl,_⟩ | ⟨s,rfl,_⟩ | ⟨s,p,q,dp,dq,rfl,_⟩ |
    ⟨s,p,q,dpq,rfl,_⟩ | ⟨s,p,dp,rfl,_⟩ | ⟨s,p,t,dp,rfl,_⟩ |
    ⟨s,dp,rfl,_⟩ | ⟨s,dp,rfl,_⟩ | ⟨s,p,dp,dq,rfl,_⟩ | ⟨s,p,rfl,_⟩ <;>
    simp [axL,verumIntro,andIntro,orIntro,allIntro,exsIntro,wkRule,shiftRule,cutRule,axm]

theorem ordinary_derivation_member_lt {d p : V}
    (h : Derivation Presentation.ordinaryPAeq d) (hp : p∈fstIdx d) : p<d :=
  lt_trans (lt_of_mem hp)
    (RelationalSource.Numeric.fstIdx_lt_of_positive (ordinary_derivation_positive h))

theorem SourceProofBudget.descend {d child f : V} (h : SourceProofBudget d f)
    (hc : child≤d) : SourceProofBudget child f := ⟨h.1,le_trans hc h.2⟩

theorem SourceProofBudget.formula {d f p : V} (h : SourceProofBudget d f)
    (hp : IsFormula Presentation.language p) (hd : p≤d) :
    SupportedFormulaCovered 0 0 (parameters 0 f) p := by
  apply supported_coverage_of_code
  refine ⟨?_,hp,?_⟩
  · simpa [ParametersValid] using h.1
  · simpa using le_trans hd h.2

theorem SourceProofBudget.sequent {d f : V} (h : SourceProofBudget d f)
    (hd : Derivation Presentation.ordinaryPAeq d) : SupportedSet (parameters 0 f) (fstIdx d) := by
  intro p hp
  exact h.formula (hd.isFormulaSet p hp) (ordinary_derivation_member_lt hd hp).le

theorem SourceProofBudget.term {d f t : V} (h : SourceProofBudget d f)
    (ht : IsTerm Presentation.language t) (hd : t≤d) :
    NumericPAeqTerm.FreeSupported (len f) t :=
  ⟨ht.isUTerm,le_trans (NumericPAeqTerm.freeBound_le_code ht.isUTerm) (le_trans hd h.2)⟩

theorem SourceProofBudget.eigen_child {d child f : V} (h : SourceProofBudget d f)
    (hc : child≤d) : SourceProofBudget child
      (NumericPAeqUniversalContextOpening.eigenEnvironment f) := by
  refine ⟨NumericPAeqUniversalContextOpening.eigenEnvironment_valid h.1,?_⟩
  have hh : child≤len f+1 := le_trans (le_trans hc h.2) (by simp)
  simpa [NumericPAeqUniversalContextOpening.eigenEnvironment,
    NumericPAeqTerm.targetShiftTerms_length h.1] using hh

#print axioms sourceProofBudget_graph
#print axioms ordinary_derivation_positive
#print axioms ordinary_derivation_member_lt
#print axioms SourceProofBudget.descend
#print axioms SourceProofBudget.formula
#print axioms SourceProofBudget.sequent
#print axioms SourceProofBudget.term
#print axioms SourceProofBudget.eigen_child
end M6.PA.NumericPAeqFormula.Sequent

