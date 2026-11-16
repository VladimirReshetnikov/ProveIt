module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.PAInterpretedFixedSeedModels
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.ForwardRelational

namespace PA196.Arithmetic.Transport.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal (Term Formula)
open PA196.Arithmetic.Checker PA196.Arithmetic.Certificates
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

/-- A fixed standard interpreted axiom now has an accepted certificate at
arbitrary model-valued valid finite labels, allocator and reserve. -/
theorem fixedImage_relocated_certificate (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms)
    (f lo z : V)
    (h : Numeric.FormulaCovered 0 f lo z
      (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : V)) :
    ∃ code : V, verifyValue code=
      Numeric.translate (Numeric.parameters 0 f lo z)
        (⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝ : V)+1 := by
  let q : V := ⌜formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))⌝
  have hq := NumericPAeqFormula.fixed_interpretation_quote_closed (V:=V) p hp (fun _ => (.fvar 0 : Term 0))
  have hcal : Numeric.translate (Numeric.parameters 0 (Numeric.zeroEnvironment q) 1 (fixedImageReserve p hp)) q=
      (fixedImageNativeCode p hp:V) := by
    rw [← Numeric.translate_closed_free_environments q 0 0 (Numeric.zeroEnvironment q) 1
      (fixedImageReserve p hp) hq.1.isUFormula hq.2]
    exact fixedImageSeed_translate_models p hp
  obtain ⟨seed,hs⟩ := PA196.Arithmetic.Fixed.fixed_all_models (V:=V) (fixedImageNativeProof p hp)
  obtain ⟨forward,backward,hforward,hbackward⟩ :=
    Numeric.closed_formula_parameter_certificates q (Numeric.zeroEnvironment q) 1 (fixedImageReserve p hp)
      f lo z hq.2 (fixedImageSeed_coverage p hp) h
  have hs' : verifyValue seed=Numeric.translate (Numeric.parameters 0 (Numeric.zeroEnvironment q) 1 (fixedImageReserve p hp)) q+1 := by
    rw [hcal]
    exact hs
  exact ⟨mpCertificate (Numeric.translate (Numeric.parameters 0 f lo z) q) seed forward,
    verify_mp _ _ _ _ hs' hforward⟩

#print axioms fixedImage_relocated_certificate
end PA196.Arithmetic.Transport.ForwardRelational

