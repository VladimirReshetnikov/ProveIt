module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeBoundSupport
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem bvVector_two {L : Language} [L.Encodable] [L.LORDefinable] {s t : V}
    (hs : IsUTerm L s) (ht : IsUTerm L t) :
    termBVVec L (2:V) (s∷t∷0)=termBV L s∷termBV L t∷0 := by
  simpa [one_add_one_eq_two,ht] using termBVVec_cons (k:=(1:V)) (ts:=t∷0) hs (by simp [ht])

theorem equality_bv {s t : V} (hs : IsUTerm Presentation.language s) (ht : IsUTerm Presentation.language t) :
    bv Presentation.language (equalityCode s t)=max (termBV Presentation.language s) (termBV Presentation.language t) := by
  simp [equalityCode,Presentation.source_relations,hs,ht]

theorem less_arity_iff {n s t : V} (hs : IsUTerm Presentation.language s) (ht : IsUTerm Presentation.language t) :
    IsSemiformula Presentation.language n (lessCode s t) ↔
      IsSemiterm Presentation.language n s ∧ IsSemiterm Presentation.language n t := by
  simp only [lessCode,equalityCode,IsSemiformula.exs,IsSemiformula.rel,
    Presentation.source_relations,IsSemitermVec.doubleton,IsSemiterm.func,Presentation.source_functions]
  simp [IsSemiterm.def,hs,ht,hs.termBShift,ht.termBShift,termBV_termBShift_le]

theorem less_bv {s t : V} (hs : IsUTerm Presentation.language s) (ht : IsUTerm Presentation.language t) :
    bv Presentation.language (lessCode s t)=max (termBV Presentation.language s) (termBV Presentation.language t) := by
  have hvalid : IsSemiformula Presentation.language (max (termBV Presentation.language s) (termBV Presentation.language t)) (lessCode s t) :=
    (less_arity_iff hs ht).mpr ⟨⟨hs,le_max_left _ _⟩,⟨ht,le_max_right _ _⟩⟩
  apply le_antisymm hvalid.bv_le
  have h := (less_arity_iff hs ht).mp hvalid.isUFormula.isSemiformula
  exact max_le h.1.bv h.2.bv

#print axioms bvVector_two
#print axioms equality_bv
#print axioms less_arity_iff
#print axioms less_bv
end M6.PA.FoundationPAeqCode

