import DiophantineConsistency.CleanMaskClasses
import DiophantineConsistency.CompactDummyBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanModelSupport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryCarry ArithmeticWindowDigits CompactSymbolicPorts
open CleanGeometry CleanMaskClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_outside (n C : V)
    (hslots : ∀ k<n, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) :
    ∀ k<n, ¬Bad (k%8807) → dig 67 C k=0 := by
  intro k hi hbad
  have hi0 : 0<k := by
    by_contra hz
    have he : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hz)
    subst k
    apply hbad
    left
    simp
  have hmod : k%8807<8807 := mod_lt _ (by norm_num)
  obtain ⟨j,hj,hjv⟩ := bounded_standard 8807 (k%8807) hmod
  have hbadnat : ¬BadNat j := by
    intro hb
    apply hbad
    rw [hjv,bad_cast]
    exact hb
  have hmem : j∉CompactConcreteMask.support := by
    intro hm
    exact hbadnat (support_subset_bad j hm)
  have hspecial : j≠1063 := by
    intro he
    apply hbadnat
    unfold BadNat
    rw [he]
    left
    omega
  have hn := hslots k hi hi0
  rw [hjv,absent_mask_digit j hj hmem hspecial] at hn
  exact CompactDummyBound.forbidden_zero _ (dig_lt 67 C k) hn

theorem boolean_away_special (n C : V) (h0 : dig 67 C 0≤1)
    (hslots : ∀ k<n, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) :
    ∀ k<n, k%8807≠1063 → dig 67 C k≤1 := by
  intro k hi hspecial
  by_cases hi0 : k=0
  · simpa only [hi0] using h0
  · have hipos : 0<k := by
      by_contra hz
      exact hi0 (nonpos_iff_eq_zero.mp (not_lt.mp hz))
    have hmod : k%8807<8807 := mod_lt _ (by norm_num)
    obtain ⟨j,hj,hjv⟩ := bounded_standard 8807 (k%8807) hmod
    have hjsp : j≠1063 := by
      intro he
      apply hspecial
      rw [hjv,he]
      norm_num
    have hn := hslots k hi hipos
    by_cases hmem : j∈CompactConcreteMask.support
    · rw [hjv,ordinary_mask_digit j hj hmem hjsp] at hn
      exact CompactDummyBound.ordinary_le_one _ (dig_lt 67 C k) hn
    · rw [hjv,absent_mask_digit j hj hmem hjsp] at hn
      have hz := CompactDummyBound.forbidden_zero _ (dig_lt 67 C k) hn
      rw [hz]
      norm_num
#print axioms CleanModelSupport.zero_outside
#print axioms CleanModelSupport.boolean_away_special
end CleanModelSupport
