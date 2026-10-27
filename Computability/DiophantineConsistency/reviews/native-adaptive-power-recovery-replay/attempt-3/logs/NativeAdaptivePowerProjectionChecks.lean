import DiophantineConsistency.NativeAdaptivePowerProjection

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptivePowerProjectionChecks
open NativeAdaptivePowerProjection NativeAdaptiveMainBootstrap

-- The signed difference, rather than an assumed nonnegative quotient, is used.
example {Q n : ℕ} {E k R : ℤ} (hQ : 0<Q) (hEP : E ∣ 2*(Q:ℤ))
    (hwin : R+1<E) (hnR : (n:ℤ)<R)
    (hk : k=2*(Pell.yn (by omega : 1<2*Q+1) n:ℤ))
    (hv : E ∣ k-R-1) : 2*(n:ℤ)=R+1 :=
  first_index_exact_signed hQ hEP hwin hnR hk hv

-- A multiple-of-three base is retained by the projection client.
example {X k eta gamma t D : ℤ}
    (hD : mainDstar 3 X 27 k eta gamma (3^2*27*t)=3^2*27*D) :
    (4*27*(X+1)+3) ∣ 3*(D-X-27*(X+1)*(k*27+eta)) ∧ (3:ℤ) ∣ 3*X := by
  apply scaled_projection_algebra (by norm_num) (by norm_num)
    (show (3:ℤ)^3 ∣ 27 from ⟨1,by norm_num⟩) ⟨t,rfl⟩ hD

-- Literal ring witnesses carry no sign or coprimality assumption.
example (q H h0 L B : ℤ) (hH : H=q*h0+3) (hB : q*L=H*B) :
    3*L=H*(L-h0*B) := by
  rw [hH] at hB ⊢
  linear_combination -h0*hB

#print axioms first_index_exact_signed
#print axioms first_difference_four
#print axioms scaled_projection_algebra
#print axioms pell_projection
#print axioms adaptive_projection

end DiophantineConsistency.NativeAdaptivePowerProjectionChecks
