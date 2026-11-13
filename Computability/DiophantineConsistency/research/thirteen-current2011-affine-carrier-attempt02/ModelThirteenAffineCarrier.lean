import DiophantineConsistency.ModelThirteenCarrierPrelude
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The signed auxiliary ordinate yields a positive affine carrier. -/
theorem positive_affine_carrier (b u y e4 : V) (G g : DiffRing V)
    (hb : 0 < b) (hG : 0 < G) (hGb : G = ι b * g)
    (he4 : y + 1 = 4 * b * e4)
    (hsmall : |-(ι y : DiffRing V)| < 2 * |(ι u : DiffRing V)|) :
    ∃ m : DiffRing V, 0 < m ∧
      -(ι y : DiffRing V) = 1 + 4 * (ι b * (m - (ι u) ^ 2 * G) - G) := by
  set m : DiffRing V := -ι e4 + (1 + ι b * (ι u) ^ 2) * g
  have hym : -(ι y : DiffRing V) = 1 + 4 * (ι b * (m - (ι u) ^ 2 * G) - G) := by
    have e := congrArg (ι : V →+* DiffRing V) he4
    simp only [map_add, map_mul, map_one, map_ofNat] at e
    rw [hGb]
    simp only [m]
    linear_combination -e
  have hsm : -2 * ι u < -(ι y : DiffRing V) := by
    have h := neg_abs_le (-(ι y : DiffRing V))
    have hu0 : |(ι u : DiffRing V)| = ι u := abs_of_nonneg (ι_nonneg u)
    linarith only [h, hu0, hsmall]
  exact ⟨m, ModelThirteenRestoration.affine_carrier_pos modelFacts (ι_pos hb) hG hsm hym, hym⟩

end DiophantineConsistency.ModelThirteenCarrier
#print axioms DiophantineConsistency.ModelThirteenCarrier.positive_affine_carrier
