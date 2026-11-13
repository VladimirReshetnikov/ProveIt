module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.PAInterpretedFixedRelocation
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.ForwardRelational

namespace PA196.Arithmetic.Transport.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal (Term Formula)
open PA196.Arithmetic.Checker
attribute [local irreducible] Numeric.coverageGraph Numeric.translateGraph Numeric.parametersGraph
noncomputable def fixedImageCertificateSentence (p : SourceFormula 0) : ArithmeticSentence :=
  let q := Encodable.encode (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0)))
  “∀ f lo z, !Numeric.coverageGraph 0 f lo z ↑q →
    ∃ param out code, !Numeric.parametersGraph param 0 f lo z ∧
      !Numeric.translateGraph out param ↑q ∧ !verifyGraph (out+1) code”
theorem pa_proves_fixedImageInternal (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    theory ⊢ fixedImageCertificateSentence p := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [fixedImageCertificateSentence,models_iff,Numeric.coverage_graph,
    Numeric.parameters_graph,Numeric.translate_graph,verify_graph,Matrix.comp_vecCons'',numeral_eq_natCast]
  intro f lo z h
  have hh : Numeric.FormulaCovered (0:V) f lo z
      (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : V) := by
    simpa only [Semiformula.quote_eq_encode] using h
  obtain ⟨code,hcode⟩ := fixedImage_relocated_certificate p hp f lo z hh
  exact ⟨code,by simpa only [Semiformula.quote_eq_encode] using hcode.symm⟩

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
/-- The actual coded arithmetic interpretation is consumed, not an assumed
identification with a different target encoding. -/
theorem fixedImage_twoStage_certificate (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms)
    (arithmeticParam f lo z : V)
    (hv : NumericPAeqFormula.ParametersValid 0 0 arithmeticParam)
    (h : Numeric.FormulaCovered 0 f lo z
      (NumericPAeqFormula.formulaSyntax arithmeticParam (⌜p⌝ : V))) :
    ∃ code : V, verifyValue code=Numeric.translate (Numeric.parameters 0 f lo z)
      (NumericPAeqFormula.formulaSyntax arithmeticParam (⌜p⌝ : V))+1 := by
  have he := NumericPAeqFormula.formulaSyntax_closed_source_quote
    (fixedAxiom_freeVariables p hp) arithmeticParam hv
  rw [he] at h ⊢
  exact fixedImage_relocated_certificate p hp f lo z h
#print axioms pa_proves_fixedImageInternal
#print axioms fixedImage_twoStage_certificate
end PA196.Arithmetic.Transport.ForwardRelational

