module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFreeSupportSubstitution
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
theorem freeBound_eq_zero_of_shift_fixed {t:V} (ht:IsUTerm L t) (he:termShift L t=t):freeBound t=0 := by
  have hall : ∀t:V,IsUTerm L t→termShift L t=t→freeBound t=0 := by
    apply IsUTerm.induction 𝚺 (P:=fun t:V=>termShift L t=t→freeBound t=0)
    · definability
    · intro i h; simp
    · intro i h
      have hi : i+1=i := by simpa using h
      exact False.elim (ne_of_gt (lt_add_one i) hi)
    · intro k f v hf hv ih h
      have he : termShiftVec L k v=v := by simpa [termShift_func hf hv] using h
      rw [freeBound_func hf hv]
      apply le_antisymm
      · apply listMaxss_le_iff.mpr
        intro i hi
        have hik:i<k := by simpa [hv] using hi
        rw [freeBoundVec_nth hv hik]
        have htfix : termShift L (nth v i)=nth v i := by
          have he' := congrArg (fun x:V=>nth x i) he
          simpa only [nth_termShiftVec hv hik] using he'
        rw [ih i hik htfix]
      · simp
  exact hall t ht he

theorem freeSupported_zero_of_shift_fixed {t:V} (ht:IsUTerm L t) (he:termShift L t=t):FreeSupported 0 t :=
  ⟨ht,by rw [freeBound_eq_zero_of_shift_fixed ht he]⟩
#print axioms freeBound_eq_zero_of_shift_fixed
#print axioms freeSupported_zero_of_shift_fixed
end M6.PA.NumericPAeqTerm

