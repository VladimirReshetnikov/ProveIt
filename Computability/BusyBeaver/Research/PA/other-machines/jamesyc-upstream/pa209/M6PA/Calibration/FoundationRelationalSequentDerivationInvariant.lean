module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentShiftRule
@[expose] public section

/-! Explicit arithmetic invariant for conditional translation of the unchanged
relational Foundation derivation codes. The axiom supplier is a separate
assumption, not an implementation of the original arithmetic theory images. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint

attribute [local irreducible] parametersGraph translateGraph sequentGraph verifyGraph coverageGraph proofEnvironmentGraph
noncomputable def derivationCertificateGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “code d f lo z. ∃ s param out, !fstIdxDef s d ∧ !parametersGraph param 0 f lo z ∧
    !sequentGraph out param s ∧ !verifyGraph (out+1) code”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem derivationCertificate_graph (code d f lo z : V) :
    derivationCertificateGraph.val.Evalb ![code,d,f,lo,z] ↔
      verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx d)+1 := by
  simp [derivationCertificateGraph,parameters_graph,sequent_graph,verify_graph,Matrix.comp_vecCons'',eq_comm]

variable (T : Theory language) [T.Δ₁]

noncomputable def axiomCertificateSupplier : ArithmeticSentence :=
  “∀ p f lo z, !T.Δ₁ch.sigma p → !coverageGraph 0 f lo z p →
    ∃ param out code, !parametersGraph param 0 f lo z ∧ !translateGraph out param p ∧
      !verifyGraph (out+1) code”

def AxiomCertificateSupplier : Prop := ∀ p f lo z : V,
  p∈T.Δ₁Class → FormulaCovered 0 f lo z p →
    ∃ code, verifyValue code=translate (parameters 0 f lo z) p+1

theorem axiomCertificateSupplier_semantics :
    (axiomCertificateSupplier T).Evalb (![] : Fin 0 → V) ↔ AxiomCertificateSupplier (V:=V) T := by
  simp [axiomCertificateSupplier,AxiomCertificateSupplier,coverage_graph,parameters_graph,
    translate_graph,verify_graph,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] derivationCertificateGraph
noncomputable def derivationTranslationInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ d<n, !(derivation T).sigma d → ∀ f lo z, !proofEnvironmentGraph d f lo z →
    ∃ code, !derivationCertificateGraph code d f lo z”

theorem derivationTranslation_invariant (n : V) :
    (derivationTranslationInvariant T).Evalb ![n] ↔
    ∀ d<n, Derivation T d → ∀ f lo z : V, ProofEnvironment d f lo z →
      ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) (fstIdx d)+1 := by
  simp [derivationTranslationInvariant,proofEnvironment_graph,derivationCertificate_graph,Matrix.comp_vecCons'']

#print axioms derivationCertificate_graph
#print axioms axiomCertificateSupplier_semantics
#print axioms derivationTranslation_invariant
end M6.PA.RelationalSource.Numeric

