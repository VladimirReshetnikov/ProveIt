import PA194RankedOpenSeparation

/-! Internal structural induction for arbitrary-label vacuity. -/
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
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The same coded separation root, defined for every arithmetic model. -/
noncomputable def sepRootPure (p : V) : V :=
  ^∀ (^∃ (^∀
    (((^nrel (2 : V) (1 : V) (?[ ^#(0 : V), ^#(1 : V)] : V)) ^⋎
       ((^rel (2 : V) (1 : V) (?[ ^#(0 : V), ^#(2 : V)] : V)) ^⋏ p)) ^⋏
     (((^nrel (2 : V) (1 : V) (?[ ^#(0 : V), ^#(2 : V)] : V)) ^⋎ neg SourceL p) ^⋎
       (^rel (2 : V) (1 : V) (?[ ^#(0 : V), ^#(1 : V)] : V))))))

/-- Parameter-free arithmetic graph for the separation-root constructor. -/
noncomputable def sepRootGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “q p. ∃ n, !(negGraph SourceL) n p ∧
    ∃ z0, !qqBvarDef z0 0 ∧ ∃ z1, !qqBvarDef z1 1 ∧ ∃ z2, !qqBvarDef z2 2 ∧
    ∃ t1, !adjoinDef t1 z1 0 ∧ ∃ v01, !adjoinDef v01 z0 t1 ∧
    ∃ t2, !adjoinDef t2 z2 0 ∧ ∃ v02, !adjoinDef v02 z0 t2 ∧
    ∃ a, !qqNRelDef a 2 1 v01 ∧ ∃ b, !qqRelDef b 2 1 v02 ∧
    ∃ c, !qqNRelDef c 2 1 v02 ∧ ∃ d, !qqRelDef d 2 1 v01 ∧
    ∃ e, !qqAndDef e b p ∧ ∃ f, !qqOrDef f a e ∧
    ∃ g, !qqOrDef g c n ∧ ∃ h, !qqOrDef h g d ∧
    ∃ j, !qqAndDef j f h ∧ ∃ k, !qqAllDef k j ∧
    ∃ l, !qqExsDef l k ∧ !qqAllDef q l”

theorem sepRootGraph_defined : 𝚺₁-Function₁ (sepRootPure : V → V) via sepRootGraph := .mk fun v => by
  simp [sepRootGraph,sepRootPure, ←adjoin_def]

/-- Uniform parameter-free Δ₁ formula for shift-invariant separation roots. -/
noncomputable def closedSepUniform : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “q. ∃ p <⁺ q, !(isSemiformula SourceL).sigma 1 p ∧
    !(shiftGraph SourceL) p p ∧ !sepRootGraph q p”)
  (.mkPi “q. ∃ p <⁺ q, !(isSemiformula SourceL).pi 1 p ∧
    !((shiftGraph SourceL).graphDelta.pi) p p ∧ !(sepRootGraph.graphDelta.pi) q p”)

noncomputable def closedSepPure (q : V) : Prop :=
  ∃ p ≤ q, IsSemiformula SourceL 1 p ∧ shift SourceL p = p ∧ sepRootPure p = q

theorem closedSepUniform_defined : 𝚫₁-Predicate (closedSepPure : V → Prop) via closedSepUniform := by
  haveI : 𝚺₁-Function₁ (sepRootPure : V → V) via sepRootGraph := sepRootGraph_defined
  haveI : 𝚫₁-Function₁ (sepRootPure : V → V) via sepRootGraph.graphDelta :=
    HierarchySymbol.DefinedFunction.graph_delta sepRootGraph_defined
  haveI : 𝚫₁-Function₁ (shift SourceL : V → V) via (shiftGraph SourceL).graphDelta :=
    HierarchySymbol.DefinedFunction.graph_delta (shift.defined (L := SourceL))
  refine ⟨?_⟩
  constructor
  · intro v
    simp [closedSepUniform, HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_pi, HierarchySymbol.Defined.iff_delta_sigma]
  · intro v
    simp [closedSepUniform, closedSepPure, HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_sigma, eq_comm]

/-- IΣ₁ proves that the two classifier polarities agree. -/
theorem closedSepUniform_provablyProper : closedSepUniform.ProvablyProperOn 𝗜𝚺₁ := by
  apply HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0}
  intro W _ _
  letI : 𝚫₁-Predicate (closedSepPure : W → Prop) via closedSepUniform := closedSepUniform_defined
  exact HierarchySymbol.Defined.proper

#print axioms closedSepUniform_provablyProper
#print axioms closedSepUniform_defined
#print axioms sepRootGraph_defined
end generic
end PA194ModelLogic
