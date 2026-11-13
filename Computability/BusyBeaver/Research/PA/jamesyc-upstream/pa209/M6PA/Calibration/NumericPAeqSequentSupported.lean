module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentValidity
public import M6PA.Calibration.FoundationRelationalSequentFold
@[expose] public section

namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

def SupportedSet (param s : V) : Prop :=
  ∀ p, p∈s → SupportedFormulaCovered 0 0 param p

attribute [local irreducible] supportedCoverageGraph
noncomputable def supportedSetGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “param s. ∀ p<s, p∈s → !supportedCoverageGraph 0 0 param p”

theorem supportedSet_graph (param s : V) : supportedSetGraph.val.Evalb ![param,s] ↔
    SupportedSet param s := by
  simp only [supportedSetGraph,Bounding.HierarchySymbol.Semiformula.val_mkSigma]
  simp [supportedCoverage_graph,SupportedSet,Matrix.comp_vecCons'']
  exact ⟨fun h p hp => h p (lt_of_mem hp) hp,fun h p _ hp => h p hp⟩

theorem SupportedSet.member_valid {param s p : V} (h : SupportedSet param s) (hp : p∈s) :
    IsUFormula language (formulaSyntax param p) :=
  (formulaSyntax_supported_isSemiformula (h p hp)).isUFormula

theorem SupportedSet.scan_valid {param s : V} (h : SupportedSet param s) (n : V) :
    IsUFormula language (sequentScan param s n) :=
  (sequentScan_valid param s n 0 0 h).isUFormula

#print axioms supportedSet_graph
#print axioms SupportedSet.member_valid
#print axioms SupportedSet.scan_valid
end M6.PA.NumericPAeqFormula.Sequent

