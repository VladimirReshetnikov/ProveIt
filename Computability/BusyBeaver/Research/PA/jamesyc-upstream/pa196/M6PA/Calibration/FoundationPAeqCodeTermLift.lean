module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermBShift
public import M6PA.Calibration.FoundationPAeqCodeTermSubstitution
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termVector_qVec {k w : V} (hw : IsUTermVec ℒₒᵣ k w) :
    termVector (k+1) (qVec ℒₒᵣ w)=qVec Presentation.language (termVector k w) := by
  simp only [qVec,termVector_length hw,←hw.lh]
  rw [termVector_cons (by simp) hw.termBShiftVec,termCode_bvar,termVector_bShift hw]

#print axioms termVector_qVec
end M6.PA.FoundationPAeqCode
