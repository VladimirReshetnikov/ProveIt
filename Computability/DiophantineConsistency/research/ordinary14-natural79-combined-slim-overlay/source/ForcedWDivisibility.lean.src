import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-! Source-only commutative-ring algebra for the proposed forced-w model
route. This file does not assert any graph, model, or endpoint hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ForcedWDivisibilityDraft

/-- A Pell norm makes `d-a*c` invertible modulo H, so its U-multiple being
divisible by H implies H divides U. All hypotheses are explicit. -/
theorem divisor_of_main_norm {R : Type*} [CommRing R] (H U d a c : R)
    (hdiv : H ∣ U*(d-a*c))
    (hnorm : d*d=1+(a*a+H)*c*c) : H ∣ U := by
  obtain ⟨z,hz⟩ := hdiv
  refine ⟨z*(d+a*c)-U*c*c,?_⟩
  calc
    U=U*(d*d-a*a*c*c)-U*H*c*c := by rw [hnorm]; ring
    _=(U*(d-a*c))*(d+a*c)-U*H*c*c := by ring
    _=H*(z*(d+a*c)-U*c*c) := by rw [hz]; ring

/-- The concrete identities H=4Y+3 and U=Yq² propagate H|U to H|3q². -/
theorem divisor_of_three_square {R : Type*} [CommRing R] (H U q Y : R)
    (hH : H=4*Y+3) (hU : U=Y*q*q) (hdiv : H ∣ U) : H ∣ 3*q*q := by
  obtain ⟨z,hz⟩ := hdiv
  refine ⟨q*q-4*z,?_⟩
  calc
    3*q*q=(4*Y+3)*q*q-4*(Y*q*q) := by ring
    _=H*q*q-4*U := by rw [hH,hU]
    _=H*(q*q-4*z) := by rw [hz]; ring

end DiophantineConsistency.ForcedWDivisibilityDraft

#print axioms DiophantineConsistency.ForcedWDivisibilityDraft.divisor_of_main_norm
#print axioms DiophantineConsistency.ForcedWDivisibilityDraft.divisor_of_three_square
