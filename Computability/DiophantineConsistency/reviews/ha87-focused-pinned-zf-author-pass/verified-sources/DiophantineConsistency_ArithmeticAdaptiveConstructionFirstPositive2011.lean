import DiophantineConsistency.ArithmeticAdaptiveConstructionCarrier2011

/-! A positive first carrier under explicit size hypotheses. The hypotheses
are separate obligations of the actual reverse construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstPositive2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveConstructionCarrier2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive first Pell root strictly exceeds its linear leading term. -/
theorem leading_lt_first_root (Q k tau : V)
    (hnorm : tau*tau=1+Q*(Q+1)*k*k) : Q*k<tau := by
  apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _)
  rw [hnorm]
  calc (Q*k)*(Q*k) ≤ (Q*k)*(Q*k)+Q*k*k := le_add_of_nonneg_right (by simp)
       _ < (Q*k)*(Q*k)+Q*k*k+1 := lt_add_one _
       _ = 1+Q*(Q+1)*k*k := by ring

/-- If the transport quotient is nonzero and the old ordinate scale is at
most k, the first carrier has a positive input with the exact scaled root. -/
theorem positive_first_carrier (q Q k sY b tau : V)
    (hq : 2≤q-1) (hb : 1≤b) (hs : sY≤k)
    (hnorm : tau*tau=1+Q*(Q+1)*k*k) :
    ∃ r : V, 0<r ∧
      let ell := Q*k
      let Y := q^3*sY
      ell+k+r+sY=(1+(q-1)*k)*b+tau ∧
      (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
        (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*b) := by
  have hroot := leading_lt_first_root Q k tau hnorm
  have hW : k+sY≤(1+(q-1)*k)*b := by
    calc k+sY ≤ k+k := add_le_add le_rfl hs
         _ = 2*k := by ring
         _ ≤ (q-1)*k := mul_le_mul_of_nonneg_right hq (by simp)
         _ ≤ 1+(q-1)*k := le_add_of_nonneg_left (by simp)
         _ ≤ (1+(q-1)*k)*b := le_mul_of_one_le_right (by simp) hb
  have hlt : Q*k+k+sY < (1+(q-1)*k)*b+tau := by
    have hsum := add_lt_add_of_lt_of_le hroot hW
    simpa only [add_assoc, add_comm, add_left_comm] using hsum
  let r := (1+(q-1)*k)*b+tau-(Q*k+k+sY)
  have hr : 0<r := tsub_pos_iff_lt.mpr hlt
  have he : Q*k+k+r+sY=(1+(q-1)*k)*b+tau := by
    have hc := tsub_add_cancel_of_le (le_of_lt hlt)
    dsimp only [r]
    calc Q*k+k+((1+(q-1)*k)*b+tau-(Q*k+k+sY))+sY =
         ((1+(q-1)*k)*b+tau-(Q*k+k+sY))+(Q*k+k+sY) := by ring
         _ = (1+(q-1)*k)*b+tau := hc
  refine ⟨r,hr,he,?_⟩
  exact first_carrier_cut q (Q*k) k r sY b tau he
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstPositive2011
