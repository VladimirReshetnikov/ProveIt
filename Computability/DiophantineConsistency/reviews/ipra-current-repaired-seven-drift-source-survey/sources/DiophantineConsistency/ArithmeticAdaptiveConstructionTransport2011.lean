import DiophantineConsistency.ArithmeticAdaptiveWindow2011

/-! Transport identity for the reverse adaptive witness construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionTransport2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- From the old transport equation, recover the adaptive graph's transport
cut. The subtractions are justified by the displayed cancellation identities;
no solution, norm, power, or unproved witness is assumed. -/
theorem adaptive_transport_cut (q K w F alpha C z : V)
    (hq : q-1+1=q) (hz : z-1+1=z) (hC : F+alpha+C=q)
    (ht : (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1) :
    (q*K+q*w)*C=q*F+(q-1)*(q*(z-1)) := by
  have htrans : (K+w)*C=F+(z-1)*(q-1) := by
    have h1 : (K+w)*(F+alpha)+((K+w)*C+(q-1)+1) =
        (K+w)*(F+alpha)+(F+(z-1)*(q-1)+(q-1)+1) := by
      calc
        _=(K+w)*(F+alpha+C)+(q-1+1) := by ring
        _=(K+w)*q+q := by rw [hC,hq]
        _=(K+w)*(F+alpha)+F+z*(q-1)+1 := ht
        _=_ := by
          conv_lhs => rw [←hz]
          ring
    exact add_right_cancel (add_right_cancel (add_left_cancel h1))
  calc
    (q*K+q*w)*C=q*((K+w)*C) := by ring
    _=q*(F+(z-1)*(q-1)) := by rw [htrans]
    _=q*F+(q-1)*(q*(z-1)) := by ring
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticMaskConstants
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

/-- The old equation system supplies the adaptive transport cut on its actual
coordinates, including positivity of the gap. This is only the transport part
of the reverse witness construction. -/
theorem adaptive_transport_of_equations (u : Fin 14 → V) (hu : ∀ j, 0<u j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) u) :
    let q := ArithmeticCarrierRadix2011.q u
    let C := q-u 1-u 2
    0<C ∧ (q*(CurrentKernel2011.K:V)+q*u 8)*C =
      q*u 1+(q-1)*(q*(u 3-1)) := by
  dsimp only
  obtain ⟨hb,hl,hh⟩ := current_bounds (V:=V)
  have ht := he.1
  have hgap := (ArithmeticPellFirstIndex.scalar_window (ArithmeticCarrierRadix2011.q u)
      (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
      ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (u 0) (u 1) (u 2) (u 3) (u 8) (u 7) (lt_of_lt_of_le (by norm_num) hb)
      (hu 0) (hu 1) (hu 2) (hu 3) (hu 8) (hu 7) hl hh rfl ht).1
  have hlt : u 1+u 2 < ArithmeticCarrierRadix2011.q u :=
    tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
  have hq : ArithmeticCarrierRadix2011.q u-1+1=ArithmeticCarrierRadix2011.q u :=
    tsub_add_cancel_of_le (le_trans (pos_iff_one_le.mp (hu 1))
      (le_trans (by simp) (le_of_lt hlt)))
  have hz : u 3-1+1=u 3 := tsub_add_cancel_of_le (pos_iff_one_le.mp (hu 3))
  have hC : u 1+u 2+(ArithmeticCarrierRadix2011.q u-u 1-u 2)=ArithmeticCarrierRadix2011.q u := by
    rw [tsub_tsub]
    exact add_tsub_cancel_of_le (le_of_lt hlt)
  exact ⟨hgap,adaptive_transport_cut _ _ _ _ _ _ _ hq hz hC ht⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionTransport2011
