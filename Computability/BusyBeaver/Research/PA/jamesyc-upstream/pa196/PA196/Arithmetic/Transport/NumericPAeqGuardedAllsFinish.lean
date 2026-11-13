module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqGuardedAlls
public import M6PA.Calibration.NumericPAeqFormulaClosedEnvironment
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryEmptyRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqGuardedAlls
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqValueTotality RelationalPredicateBinary
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem closed_matrix_certificate {p:V} (hp:IsFormula Presentation.language p) (hs:FreeSupported 0 p)
    (h:MatrixSupply 0 p) (f native lo z:V)
    (hc:FormulaCovered 0 native lo z (formulaSyntax (NumericPAeqFormula.parameters 0 f) p)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (formulaSyntax (NumericPAeqFormula.parameters 0 f) p)+1 := by
  rw [formulaSyntax_closed_environment hs 0 f 0] at hc ⊢
  have hv :IsFormula language (formulaSyntax (NumericPAeqFormula.parameters 0 0) p) :=
    formulaSyntax_supported_isSemiformula ⟨by simp [ParametersValid],hp,by simpa using hs⟩
  have ht :IsFormula language (inputDomain (0:V) 0 0) := by simp [inputDomain]
  apply source_certificate_mp (inputDomain 0 0 0) _ native lo z ht hv hc
  · intro g l z hc
    have d :ND.Proof (T:=(∅:Theory language).internalize V) ∅ ((⊤:SF (V:=V) 0) ⋏ ⊤) :=
      ND.andIntro (TDerivation.verum (by simp)) (TDerivation.verum (by simp))
    simpa [inputDomain] using empty_requested_certificate ((⊤:SF (V:=V) 0) ⋏ ⊤) d g l z (by simpa [inputDomain] using hc)
  · exact h 0 0 (by simp) (by simp)
#print axioms closed_matrix_certificate
end PA196.Arithmetic.Transport.NumericPAeqGuardedAlls

