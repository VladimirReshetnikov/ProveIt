module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionCalibration
@[expose] public section
/-! Exact bound-variable support, needed for canonical closure counts. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem bvVector_nil {L : Language} [L.Encodable] [L.LORDefinable] :
    termBVVec (V:=V) L 0 0=0 :=
  IsUTerm.BV.construction.resultVec_nil L ![]

@[simp] theorem bvVector_one {L : Language} [L.Encodable] [L.LORDefinable] {t : V}
    (ht : IsUTerm L t) :
    termBVVec L (1:V) (t∷0)=termBV L t∷0 := by
  simpa using termBVVec_cons (k:=0) (ts:=0) ht (by simp)

theorem termCode_bv {t : V} (ht : IsUTerm ℒₒᵣ t) :
    termBV Presentation.language (termCode t)=termBV ℒₒᵣ t := by
  apply IsUTerm.induction 𝚺 (P:=fun t=>termBV Presentation.language (termCode t)=termBV ℒₒᵣ t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i; simp
  · intro i; simp
  · intro k f ts hf hs ih
    have hv:=termVector_isUTermVec hs
    have he : termBVVec Presentation.language k (termVector k ts)=termBVVec ℒₒᵣ k ts := by
      apply nth_ext' k (by simp [hv]) (by simp [hs])
      intro i hi
      rw [nth_termBVVec hv hi,termVector_nth hs hi,nth_termBVVec hs hi]
      exact ih i hi
    rw [termCode_func hf hs,termBV_func hf hs]
    rcases (original_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have : ts=0 := by simpa using hs
      subst ts; simp [functionCode,zeroCode,Presentation.source_functions]
    · have : ts=0 := by simpa using hs
      subst ts
      simp [functionCode,oneCode,zeroCode,Presentation.source_functions]
    · simpa [functionCode,Presentation.source_functions,hv] using congrArg listMax he
    · simpa [functionCode,Presentation.source_functions,hv] using congrArg listMax he

theorem termVector_bv {k ts : V} (hs : IsUTermVec ℒₒᵣ k ts) :
    termBVVec Presentation.language k (termVector k ts)=termBVVec ℒₒᵣ k ts := by
  have hv:=termVector_isUTermVec hs
  apply nth_ext' k (by simp [hv]) (by simp [hs])
  intro i hi
  rw [nth_termBVVec hv hi,termVector_nth hs hi,nth_termBVVec hs hi]
  exact termCode_bv (hs.nth hi)

#print axioms bvVector_nil
#print axioms bvVector_one
#print axioms termCode_bv
#print axioms termVector_bv
end M6.PA.FoundationPAeqCode

