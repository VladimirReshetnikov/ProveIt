module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionAgreementTerms
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
theorem qVec_agree_on_bound {n k l m w v : V}
    (hw : IsSemitermVec L k m w) (hv : IsSemitermVec L l m v)
    (hnw : n ≤ k) (hnv : n ≤ l) (h : ∀ i < n, w.[i]=v.[i]) :
    ∀ i < n+1, (qVec L w).[i]=(qVec L v).[i] := by
  intro i hi
  rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
  · simp [qVec]
  · have hin : i<n := by simpa using hi
    have hiw : i<len w := by simpa [hw.lh] using lt_of_lt_of_le hin hnw
    have hiv : i<len v := by simpa [hv.lh] using lt_of_lt_of_le hin hnv
    simp only [qVec,nth_adjoin_succ]
    rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) hiw,
      nth_termBShiftVec (by simpa [hv.lh] using hv.isUTerm) hiv,h i hin]
#print axioms qVec_agree_on_bound
end M6.PA.FoundationPAeqCode

