module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFreeSupport
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Functions
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language

instance freeBound_definable : 𝚺ᴬ₁-Function₁ (freeBound : V→V) := freeBound_defined.to_definable

theorem freeBound_le_code {t : V} (ht : IsUTerm L t) : freeBound t≤t := by
  apply IsUTerm.induction 𝚺 (P:=fun t : V => freeBound t≤t) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simpa only [freeBound_fvar] using (succ_le_iff_lt.mpr (var_lt_qqFvar x))
  · intro k f v hf hv ih
    rw [freeBound_func hf hv]
    apply listMaxss_le_iff.mpr
    intro i hi
    have hi' : i<k := by simpa [hv] using hi
    rw [freeBoundVec_nth hv hi']
    exact le_trans (ih i hi') (nth_lt_qqFunc_of_lt (by simpa [hv.lh] using hi')).le

theorem freeSupported_of_code {l t : V} (ht : IsUTerm L t) (h : t≤l) : FreeSupported l t :=
  ⟨ht,le_trans (freeBound_le_code ht) h⟩
theorem freeSupported_mono {l m t : V} (ht : FreeSupported l t) (h : l≤m) : FreeSupported m t :=
  ⟨ht.1,le_trans ht.2 h⟩

theorem freeBound_bShift {t : V} (ht : IsUTerm L t) : freeBound (termBShift L t)=freeBound t := by
  apply IsUTerm.induction 𝚺 (P:=fun t : V => freeBound (termBShift L t)=freeBound t) ?_ ?_ ?_ ?_ t ht
  · definability
  · simp
  · simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv,freeBound_func hf hv.termBShiftVec,freeBound_func hf hv]
    congr 1
    apply nth_ext' k (freeBoundVec_length hv.termBShiftVec) (freeBoundVec_length hv)
    intro i hi
    rw [freeBoundVec_nth hv.termBShiftVec hi,nth_termBShiftVec hv hi,freeBoundVec_nth hv hi,ih i hi]

theorem freeSupported_bShift {l t : V} (ht : FreeSupported l t) : FreeSupported l (termBShift L t) :=
  ⟨ht.1.termBShift,by simpa only [freeBound_bShift ht.1] using ht.2⟩

def VectorFreeSupported (l k w : V) : Prop := IsUTermVec L k w ∧ ∀ i<k, FreeSupported l (nth w i)
theorem vectorFreeSupported_qVec {l k w : V} (h : VectorFreeSupported l k w) :
    VectorFreeSupported l (k+1) (qVec L w) := by
  refine ⟨?_,?_⟩
  · simpa [qVec,←h.1.lh] using h.1.termBShiftVec.adjoin (show IsUTerm Presentation.language (qqBvar (0:V)) by simp)
  · intro i hi
    rcases zero_or_succ i with rfl|⟨j,rfl⟩
    · simp [qVec]
    · have hj : j<k := by simpa using hi
      simpa [qVec,←h.1.lh,nth_termBShiftVec h.1 hj] using freeSupported_bShift (h.2 j hj)
#print axioms freeBound_le_code
#print axioms freeSupported_of_code
#print axioms freeBound_bShift
#print axioms freeSupported_bShift
#print axioms vectorFreeSupported_qVec
end M6.PA.NumericPAeqTerm

