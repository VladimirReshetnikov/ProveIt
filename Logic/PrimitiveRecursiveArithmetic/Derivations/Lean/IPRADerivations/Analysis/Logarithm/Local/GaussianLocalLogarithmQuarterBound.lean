import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmLinearRemainder
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference

/-!
# Late Mercator observations at arguments of modulus at most one eighth

The original dyadic log of one plus the argument has modulus at most
one quarter once the observation clock is at least four. The proof
uses its checked linear remainder and the literal rational input point.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmQuarterBound

open_ipra
open GaussianLocalLogarithmName (source point pointF data)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (qzero ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem quarter_at (p z R D : PTm n)
    (h : Γ ⊢[PRAAx] source z R D)
    (hs : Γ ⊢[PRAAx] le (num 8*R) D) (hp : Γ ⊢[PRAAx] le (num 4) p) :
    Γ ⊢[PRAAx] bounded (point p z R D) one (num 4) := by
  let U := unit p
  let V := D*D*U
  let W := ofGaussian z D
  have hu := unit_positive (Γ := Γ) p
  have hd := h.andE₁
  have hv := positive_product _ _ (positive_product _ _ hd hd) hu
  have paid : Γ ⊢[PRAAx] le (num 16) U :=
    le_congr GaussianFiniteLogarithmDyadicTail.two_four (.eqRefl _)
      (GaussianExponentialReference.unit_monotone hp)
  have rs : Γ ⊢[PRAAx] le (num 64*(R*R)) (D*D) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono hs hs)
  have old := GaussianLocalLogarithmLinearRemainder.original_linear_remainder p z R D h
  have error : Γ ⊢[PRAAx] distanceBounded (point p z R D) W one (num 8) :=
    distance_radius_mono _ _ _ _ _ _ hv (by ipra_le 7)
      (by
        apply RationalValueBounds.positive_cancel (c := num 64) (by ipra_le 63)
        ipra_le 8*𝔞 U*sl rs+32*𝔞 D^2*sl paid+24*𝔞 D^2*𝔞 U)
      old
  have w0 : Γ ⊢[PRAAx] bounded W R D :=
    GaussianRationalMetric.bounded_of_cleared W z D R D hd hd
      (GaussianRationalHorner.ofGaussian_represents z D hd)
      (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl (D*D)) h.andE₂.andE₁))
  have w : Γ ⊢[PRAAx] bounded W one (num 8) :=
    bounded_radius_mono _ _ _ _ _ hd (by ipra_le 7)
      (le_congr (by ipra_ring) (by ipra_ring) hs) w0
  have z0 := (GaussianReconstructionRoots.distance_zero_iff W one (num 8) (by ipra_le 7)).iffMpr w
  have full := distance_triangle_same _ _ _ _ _ _ (by ipra_le 7) error z0
  exact bounded_radius_mono _ _ _ _ _ (by ipra_le 7) (by ipra_le 3)
    (by ipra_le 0) ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (by ipra_le 7)).iffMp full)

theorem actual_Mercator_quarter_bound_at_late_samples_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source (var 1) (var 2) (var 3) ⋏ (le (num 8*var 2) (var 3) ⋏ le (num 4) (var 0))) ⟶
        bounded (point (var 0) (var 1) (var 2) (var 3)) one (num 4)) :=
  closeUniv 4 (.impI (quarter_at _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmQuarterBound
