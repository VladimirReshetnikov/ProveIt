module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedOpening
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem formulaSyntax_supported_unary_instance {f p m x:V}
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hs:FreeSupported (len f) p) (hx:IsSemiterm language m x):
    substs1 language x (formulaSyntax (binderParameters (parameters 0 f)) p)=
      formulaSyntax (parameters (x∷0) f) p := by
  have he : ParametersValid 0 0 (parameters (0:V) f) := by simp [ParametersValid,hf]
  have hc : SupportedFormulaCovered 1 1 (binderParameters (parameters (0:V) f)) p := by
    refine ⟨by simpa using binderParameters_valid he,hp,?_⟩
    simpa [binderParameters,NumericPAeqTerm.shiftTerms_length hf] using hs
  unfold substs1
  rw [formulaSyntax_supported_targetSubst hc (IsSemitermVec.singleton.mpr hx),
    targetSubstParameters_open_binder (show IsSemitermVec language (0:V) 0 0 by simp) hf]
#print axioms formulaSyntax_supported_unary_instance
end M6.PA.NumericPAeqFormula

