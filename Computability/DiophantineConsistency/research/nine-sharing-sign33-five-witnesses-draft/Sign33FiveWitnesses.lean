import DiophantineConsistency.Sign33GapTauRing
import DiophantineConsistency.Sign33InnerVRing
import DiophantineConsistency.Sign33AuxRing

/-! UNCOMPILED: five natural witnesses under explicit conditional premises. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33FiveWitnesses
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem five_witnesses_of_windows_and_norms
    (q F alpha E N k r a c T f i S x z y : V)
    (hq : 1≤q) (hN : 1≤N) (hgap : 0<q-F-alpha) (hr : r+2<E)
    (hc : 0<c) (hT : 0<T) (hf : 0<f) (hi : 0<i) (hhalf : 2*r<c)
    (hstrict : f*f=1+delta a*(i*c*c)*(i*c*c))
    (hS : 0<S) (hy : 0<y)
    (haux : S*S*(absdiff x z)*(absdiff x z)+y*y=1+S*S*y*y) :
    ∃ gap tau inner v negative : V,
      ι gap = (ι q-1)*(ι q-ι F)+ι alpha ∧
      ι tau = ι E*ι N+ι k-ι r ∧
      ι inner = ι c*ι T-ι r ∧
      ι v = ι f*ι f*(ι c*ι T-ι r)-ι c ∧
      ι negative = ι y*ι y-(ι x-ι z)*(ι x-ι z) := by
  obtain ⟨hgapR, htauR⟩ := Sign33GapTauRing.gap_tau_of_windows q F alpha E N k r hq hN hgap hr
  obtain ⟨hinnerR, hvR⟩ := Sign33InnerVRing.inner_v_of_window_and_strong a c T r f i hc hT hf hi hhalf hstrict
  have hnegative : 0 ≤ ι y*ι y-(ι x-ι z)*(ι x-ι z) :=
    sub_nonneg.mpr (sub_nonpos.mp (Sign33AuxRing.aux_difference_of_norm S x z y hS hy haux))
  obtain ⟨gap, hgap'⟩ := nonneg_iff.mp hgapR
  obtain ⟨tau, htau'⟩ := nonneg_iff.mp htauR
  obtain ⟨inner, hinner'⟩ := nonneg_iff.mp hinnerR
  obtain ⟨v, hv'⟩ := nonneg_iff.mp hvR
  obtain ⟨negative, hnegative'⟩ := nonneg_iff.mp hnegative
  exact ⟨gap, tau, inner, v, negative, hgap'.symm, htau'.symm, hinner'.symm, hv'.symm, hnegative'.symm⟩
end DiophantineConsistency.Sign33FiveWitnesses
#print axioms DiophantineConsistency.Sign33FiveWitnesses.five_witnesses_of_windows_and_norms
