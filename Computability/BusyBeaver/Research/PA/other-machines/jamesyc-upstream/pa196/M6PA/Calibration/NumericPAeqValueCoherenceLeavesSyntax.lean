module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceGraphs
@[expose] public section

/-! Exact leaf comparison clauses; these identities alone do not prove
coherence. Endpoint terms retain their target free parameters. -/
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def variableComparison (x y:V) : V :=
  qqAll (qqAll (imp language (qqAnd (variableValue (qqBvar 1) x) (variableValue (qqBvar 0) y))
    (NumericPAeqValueIsoGuard.isoCode (qqBvar 1) (qqBvar 0))))
noncomputable def zeroComparison : V :=
  qqAll (qqAll (imp language (qqAnd (zeroValue (qqBvar 1)) (zeroValue (qqBvar 0)))
    (NumericPAeqValueIsoGuard.isoCode (qqBvar 1) (qqBvar 0))))
theorem comparison_bvar (b c f g i:V) : comparisonCode b c f g (qqBvar i)=variableComparison (nth b i) (nth c i) := by
  simp [comparisonCode,variableComparison]
theorem comparison_fvar (b c f g i:V) : comparisonCode b c f g (qqFvar i)=variableComparison (nth f i) (nth g i) := by
  simp [comparisonCode,variableComparison]
theorem comparison_zero (b c f g:V) : comparisonCode b c f g (qqFunc 0 0 0)=zeroComparison := by
  simp [comparisonCode,zeroComparison]
attribute [local irreducible] variableValueGraph zeroValueGraph templateTwoGraph
noncomputable def variableComparisonGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out x y. ∃ r s a b pair iso body inner,
    !qqBvarDef r 1 ∧ !qqBvarDef s 0 ∧ !variableValueGraph a r x ∧ !variableValueGraph b s y ∧
    !qqAndDef pair a b ∧ !NumericPAeqValueIsoGuard.isoCodeGraph iso r s ∧
    !(impGraph language) body pair iso ∧ !qqAllDef inner body ∧ !qqAllDef out inner”
theorem variableComparison_graph (out x y:V) : variableComparisonGraph.val.Evalb ![out,x,y] ↔ out=variableComparison x y := by
  simp [variableComparisonGraph,variableComparison,variableValue_graph,
    NumericPAeqValueIsoGuard.isoCode_graph,NumericPAeqValueIsoGuard.isoCode,Matrix.comp_vecCons'']
#print axioms comparison_bvar
#print axioms comparison_fvar
#print axioms comparison_zero
#print axioms variableComparison_graph
end M6.PA.NumericPAeqValueCoherence

