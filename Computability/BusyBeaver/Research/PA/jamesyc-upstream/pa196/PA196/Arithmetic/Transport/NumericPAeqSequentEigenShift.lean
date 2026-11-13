module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentTargetShift
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextOpening
public import M6PA.Calibration.NumericPAeqFormulaSupportedSourceShift
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormula
open M6.PA.NumericPAeqFormula.Sequent


/-! The actual source setShift image changes scan order. Its interpreted fold
is related by accepted certificates to target shift of the old fold. -/
namespace PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqUniversalContextOpening (eigenEnvironment source_shift_covered)
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_length)
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource.Numeric (translate)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem shifted_empty_parameters (f : V) :
    targetShiftParameters (parameters 0 f)=parameters 0 (targetShiftTerms f) := by
  simp [targetShiftParameters,NumericPAeqTerm.targetShiftTerms]

theorem SupportedSet.eigenShift {f s : V} (hf : IsSemitermVec language (len f) 0 f)
    (h : SupportedSet (parameters 0 f) s) :
    SupportedSet (parameters 0 (eigenEnvironment f)) (setShift Presentation.language s) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_setShift_iff.mp hq
  exact source_shift_covered hf (h p hp).2.1 (by simpa using (h p hp).2.2)

theorem eigen_shift_member {f p : V}
    (h : SupportedFormulaCovered 0 0 (parameters 0 f) p) :
    formulaSyntax (parameters 0 (eigenEnvironment f)) (shift Presentation.language p)=
      formulaSyntax (targetShiftParameters (parameters 0 f)) p := by
  have ht : SupportedFormulaCovered 0 0 (targetShiftParameters (parameters 0 f)) p := by
    refine ⟨targetShiftParameters_valid h.1,h.2.1,?_⟩
    have hf : IsSemitermVec language (len f) 0 f := by simpa using h.1.2
    simpa [targetShiftParameters,targetShiftTerms_length hf] using h.2.2
  rw [shifted_empty_parameters] at ht ⊢
  exact formulaSyntax_supported_sourceShift_parameters ht (by simp)

theorem eigenShift_forward_certificate (native f s : V)
    (hf : IsSemitermVec language (len f) 0 f) (hs : SupportedSet (parameters 0 f) s) :
    ∃ code, verifyValue code=wim
      (translate native (sequentCode (parameters 0 (eigenEnvironment f)) (setShift Presentation.language s)))
      (translate native (shift language (sequentCode (parameters 0 f) s)))+1 := by
  rw [sequent_targetShift _ _ hs]
  apply sequent_eliminate_certificate native _ _ _ (hs.eigenShift hf)
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_setShift_iff.mp hq
  rw [eigen_shift_member (hs p hp)]
  exact member_certificate native _ s p hs.targetShift hp

theorem eigenShift_backward_certificate (native f s : V)
    (hf : IsSemitermVec language (len f) 0 f) (hs : SupportedSet (parameters 0 f) s) :
    ∃ code, verifyValue code=wim
      (translate native (shift language (sequentCode (parameters 0 f) s)))
      (translate native (sequentCode (parameters 0 (eigenEnvironment f)) (setShift Presentation.language s)))+1 := by
  rw [sequent_targetShift _ _ hs]
  apply sequent_eliminate_certificate native _ _ _ hs.targetShift
  intro p hp
  obtain ⟨code,hcode⟩ := member_certificate native _ _ (shift Presentation.language p)
    (hs.eigenShift hf) (shift_mem_setShift hp)
  rw [eigen_shift_member (hs p hp)] at hcode
  exact ⟨code,hcode⟩

theorem eigenShift_bicertificates (native f s : V)
    (hf : IsSemitermVec language (len f) 0 f) (hs : SupportedSet (parameters 0 f) s) :
    ∃ forward backward, BiCertificates forward backward
      (translate native (sequentCode (parameters 0 (eigenEnvironment f)) (setShift Presentation.language s)))
      (translate native (shift language (sequentCode (parameters 0 f) s))) := by
  obtain ⟨forward,hforward⟩ := eigenShift_forward_certificate native f s hf hs
  obtain ⟨backward,hbackward⟩ := eigenShift_backward_certificate native f s hf hs
  exact ⟨forward,backward,hforward,hbackward⟩

#print axioms shifted_empty_parameters
#print axioms SupportedSet.eigenShift
#print axioms eigen_shift_member
#print axioms eigenShift_forward_certificate
#print axioms eigenShift_backward_certificate
#print axioms eigenShift_bicertificates
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent

