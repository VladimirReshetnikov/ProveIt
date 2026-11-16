module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionInterpretationSyntax
public import M6PA.Calibration.NumericPAeqFormulaSuccessorInstance
public import M6PA.Calibration.NumericPAeqFormulaSupportedUnaryInstance
@[expose] public section
namespace M6.PA.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def successorMatrix (p:V):V := subst Presentation.language (successorReplacement∷0) p
noncomputable def successorProperty (f p:V):V := property f (successorMatrix p)
theorem successorMatrix_valid {p:V} (hp:IsSemiformula Presentation.language 1 p):
    IsSemiformula Presentation.language 1 (successorMatrix p) :=
  hp.subst (IsSemitermVec.singleton.mpr successorReplacement_valid)
theorem successorMatrix_supported {l p:V} (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported l p):
    FreeSupported l (successorMatrix p) := by
  apply freeSupported_subst hp (IsSemitermVec.singleton.mpr successorReplacement_valid) hs
  intro i hi
  have he : i=0 := by simpa using hi
  subst i; simpa using successorReplacement_supported l
theorem property_shift {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    shift language (property f p)=property (targetShiftTerms f) p := by
  have he : ParametersValid (0:V) 0 (parameters 0 f) := by simp [ParametersValid,hf]
  rw [property,formulaSyntax_supported_targetShift (property_covered hf hp hs),targetShiftParameters_binder he]
  simp [property,targetShiftParameters,NumericPAeqTerm.targetShiftTerms]
theorem successorProperty_valid {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    IsSemiformula language 1 (successorProperty f p) :=
  property_valid hf (successorMatrix_valid hp) (successorMatrix_supported hp hs)
theorem successorProperty_shift {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p):
    shift language (successorProperty f p)=successorProperty (targetShiftTerms f) p :=
  property_shift hf (successorMatrix_valid hp) (successorMatrix_supported hp hs)
theorem property_instance {f p m x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p) (hx:IsSemiterm language m x):
    substs1 language x (property f p)=originalFormula (x∷0) f p :=
  formulaSyntax_supported_unary_instance hf hp hs hx
theorem successorProperty_instance {f p m x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p) (hx:IsSemiterm language m x):
    substs1 language x (successorProperty f p)=substitutedFormula (x∷0) f (successorReplacement∷0) p :=
  formulaSyntax_supported_unary_instance hf (successorMatrix_valid hp) (successorMatrix_supported hp hs) hx
#print axioms successorMatrix_supported
#print axioms property_shift
#print axioms successorProperty_valid
#print axioms successorProperty_shift
#print axioms property_instance
#print axioms successorProperty_instance
end M6.PA.NumericPAeqInductionInterpretation

