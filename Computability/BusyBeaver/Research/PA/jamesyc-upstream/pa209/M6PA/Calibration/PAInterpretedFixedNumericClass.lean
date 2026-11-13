module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFixedInternal
public import M6PA.Calibration.FoundationPAeqCodeTheory
@[expose] public section
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal (Term Formula)
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem fixedAxiom_quote_univCl (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    (Encodable.encode p.univCl:V)=(⌜p⌝ : V) := by
  rw [← Sentence.quote_eq_encode,Sentence.quote_def,fixedAxiom_univCl p hp]

theorem numericFixedClass_certificate (c arithmeticParam f lo z : V)
    (hc : c∈FoundationPAeqCode.targetFixedTheory.Δ₁Class)
    (hv : NumericPAeqFormula.ParametersValid 0 0 arithmeticParam)
    (h : Numeric.FormulaCovered 0 f lo z (NumericPAeqFormula.formulaSyntax arithmeticParam c)) :
    ∃ code : V, verifyValue code=Numeric.translate (Numeric.parameters 0 f lo z)
      (NumericPAeqFormula.formulaSyntax arithmeticParam c)+1 := by
  obtain ⟨p,hp,rfl⟩ := (FoundationPAeqCode.targetFixed_mem_iff c).mp hc
  rw [fixedAxiom_quote_univCl p hp] at h ⊢
  exact fixedImage_twoStage_certificate p hp arithmeticParam f lo z hv h

attribute [local irreducible] Numeric.coverageGraph Numeric.translateGraph Numeric.parametersGraph
  NumericPAeqFormula.coverageGraph NumericPAeqFormula.formulaSyntaxGraph
noncomputable def numericFixedClassSentence : ArithmeticSentence :=
  “∀ c ap f lo z interpreted,
    !((FoundationPAeqCode.targetFixedTheory.Δ₁ch).sigma) c →
    !NumericPAeqFormula.coverageGraph 0 0 ap c →
    !NumericPAeqFormula.formulaSyntaxGraph interpreted ap c →
    !Numeric.coverageGraph 0 f lo z interpreted →
    ∃ param out code, !Numeric.parametersGraph param 0 f lo z ∧
      !Numeric.translateGraph out param interpreted ∧ !verifyGraph (out+1) code”
theorem pa_proves_numericFixedClass : theory ⊢ numericFixedClassSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [numericFixedClassSentence,models_iff,NumericPAeqFormula.coverage_graph,
    NumericPAeqFormula.formulaSyntax_graph,Numeric.coverage_graph,Numeric.parameters_graph,
    Numeric.translate_graph,verify_graph,Matrix.comp_vecCons'']
  intro c ap f lo z interpreted hc hv hi h
  subst interpreted
  have hc' : c∈FoundationPAeqCode.targetFixedTheory.Δ₁Class := hc
  obtain ⟨code,he⟩ := numericFixedClass_certificate c ap f lo z hc' hv.1 h
  exact ⟨code,he.symm⟩
#print axioms fixedAxiom_quote_univCl
#print axioms numericFixedClass_certificate
#print axioms pa_proves_numericFixedClass
end M6.PA.ForwardRelational

