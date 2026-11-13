module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentGuardedCode
public import M6PA.Calibration.NumericPAeqOrdinaryAxiomCertificate
@[expose] public section

/-! The first-order requested-parameter invariant for the existing ordinaryPAeq
Foundation derivation predicate. This module defines and characterizes the
invariant; it does not prove its induction or discharge the ten rule cases. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

attribute [local irreducible] guardedCodeGraph RelationalSource.Numeric.parametersGraph
  RelationalSource.Numeric.translateGraph verifyGraph
noncomputable def requestedCertificateGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “code f s native lo z. ∃ source param out, !guardedCodeGraph source f s ∧
    !RelationalSource.Numeric.parametersGraph param 0 native lo z ∧
    !RelationalSource.Numeric.translateGraph out param source ∧ !verifyGraph (out+1) code”

theorem requestedCertificate_graph (code f s native lo z : V) :
    requestedCertificateGraph.val.Evalb ![code,f,s,native,lo,z] ↔
    verifyValue code=RelationalSource.Numeric.translate
      (RelationalSource.Numeric.parameters 0 native lo z) (guardedCode f s)+1 := by
  simp [requestedCertificateGraph,guardedCode_graph,RelationalSource.Numeric.parameters_graph,
    RelationalSource.Numeric.translate_graph,verify_graph,Matrix.comp_vecCons'',eq_comm]

def RequestedCertificate (f s : V) : Prop := ∀ native lo z : V,
  RelationalSource.Numeric.FormulaCovered 0 native lo z (guardedCode f s) →
  ∃ code, verifyValue code=RelationalSource.Numeric.translate
    (RelationalSource.Numeric.parameters 0 native lo z) (guardedCode f s)+1

attribute [local irreducible] requestedCertificateGraph supportedSetGraph parametersGraph
  RelationalSource.Numeric.coverageGraph
noncomputable def requestedSequentFormula : ArithmeticSemisentence 2 :=
  “f s. ∀ native lo z source, !guardedCodeGraph source f s →
    !RelationalSource.Numeric.coverageGraph 0 native lo z source →
    ∃ code, !requestedCertificateGraph code f s native lo z”

theorem requestedSequent_semantics (f s : V) :
    requestedSequentFormula.Evalb ![f,s] ↔ RequestedCertificate f s := by
  simp [requestedSequentFormula,RequestedCertificate,guardedCode_graph,
    RelationalSource.Numeric.coverage_graph,requestedCertificate_graph,Matrix.comp_vecCons'']

attribute [local irreducible] requestedSequentFormula
noncomputable def derivationInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ d<bound, !((derivation Presentation.ordinaryPAeq).sigma) d →
    ∀ f n param s, !lenDef n f → !((isSemitermVec language).sigma) n 0 f →
    !parametersGraph param 0 f → !fstIdxDef s d → !supportedSetGraph param s →
    !requestedSequentFormula f s”

theorem derivationInvariant_semantics (bound : V) :
    derivationInvariant.Evalb ![bound] ↔
    ∀ d<bound, Derivation Presentation.ordinaryPAeq d → ∀ f : V,
      IsSemitermVec language (len f) 0 f → SupportedSet (parameters 0 f) (fstIdx d) →
      RequestedCertificate f (fstIdx d) := by
  simp [derivationInvariant,parameters_graph,supportedSet_graph,requestedSequent_semantics,
    Matrix.comp_vecCons'',eq_comm]
  constructor
  · intro h d hd hder f hf hs
    exact h d hd hder f (len f) (parameters 0 f) (fstIdx d) rfl hf rfl rfl hs
  · intro h d hd hder f n param s hn hf hp hs hset
    subst n
    subst param
    subst s
    exact h d hd hder f hf hset

#print axioms requestedCertificate_graph
#print axioms requestedSequent_semantics
#print axioms derivationInvariant_semantics
end M6.PA.NumericPAeqFormula.Sequent

