import IPRADerivations.Analysis.Euler.VerticalBounds.Quadrature.GaussianEulerVerticalQuadrature
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveExponentialOrder

/-!
# Vertical domination on arbitrary original compact Euler intervals

The original integrand and its native real projection have identical
evaluation clocks and meshes. The finite row comparison therefore applies
at the actual observation programs for any positive compact interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalCompactInterval

open_ipra
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerCompactAdditivity (data intervalSource nameF)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (mesh precision name_at)
open GaussianPositiveRadiusFiniteSum (boundBy bound_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianRationalHorner (positive_product qadd qzero)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open RationalValueBounds (upper upper_of_radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def correction (p C E T : PTm n) : PTm n := radiusPoint (C*num 4) (E*unit (precision p T))

theorem projected_source (z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    intervalSource (argument z) R B a C E T :=
  .andI (.andI h.andE₁.andE₁ (.andI h.andE₁.andE₂.andE₁
    (le_trans (GaussianEulerVerticalNativeProjection.norm_contraction z) h.andE₁.andE₂.andE₂))) h.andE₂

theorem original_bound (p z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    boundBy (ap2 nameF p (data z R B a C E T))
      (qadd (ap2 nameF p (data (argument z) R B a C E T)) (correction p C E T)) := by
  let L := lipschitz R E T
  have grid := GaussianEulerVerticalQuadrature.original_grid_bound (precision p T) (mesh p L T) a C E z R B
    (.andI h.andE₁.andE₁ h.andE₁.andE₂.andE₂) h.andE₂.andE₁ h.andE₁.andE₂.andE₁
    (GaussianCompactRiemannName.mesh_positive p L T)
  exact bound_congr (name_at evaluatorF p a C E L T (fixedData z B)).eqSymm
    (qadd_congr (name_at evaluatorF p a C E L T (fixedData (argument z) B)).eqSymm (.eqRefl _)) grid

theorem correction_budget (p C E T : PTm n) (h : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    le (C*num 4*unit p) (E*unit (precision p T)) := by
  have four : Γ ⊢[PRAAx] le (num 4) (unit (num 6)) :=
    le_trans (le_of_eq_add (d := num 3) (by ipra_ring)) (RationalClosure.succ_le_two_pow (num 6))
  have allowance : Γ ⊢[PRAAx] le (num 4*unit p) (unit (p+num 6)) :=
    le_congr (.eqRefl _) ((pw_add two p (num 6)).eqTrans (LeanProofs.IPRA.mul_comm _ _)).eqSymm
      (LeanProofs.IPRA.mul_le_mul_right (unit p) four)
  have timeAllowance : Γ ⊢[PRAAx] le (T*(num 4*unit p)) (unit (precision p T)) :=
    le_trans (le_congr (LeanProofs.IPRA.mul_comm _ _) (.eqRefl _) (LeanProofs.IPRA.mul_le_mul_right T allowance))
      (GaussianCompactRiemannName.precision_lower p T)
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring)
      (LeanProofs.IPRA.mul_le_mul_right (num 4*unit p) h))
    (le_congr (.eqRefl _) (LeanProofs.IPRA.mul_comm _ _) (LeanProofs.IPRA.mul_le_mul_right E timeAllowance))

theorem correction_coordinate (p C E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    upper (fstT (correction p C E T)) (fstT qzero) one (unit p) := by
  let D := E*unit (precision p T)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE (unit_positive _)
  have hP := unit_positive (Γ := Γ) p
  have norm := bounded_radius_mono (correction p C E T) (C*num 4) D one (unit p) hD hP
    (le_congr (.eqRefl _) (by dsimp only [D]; ipra_ring) (correction_budget p C E T hC)) (radius_bounded _ _ hD)
  exact upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hP
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hP).iffMpr norm))

theorem actual_original_vertical_Euler_compact_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (intervalSource (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      boundBy (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (qadd (ap2 nameF (var 0) (data (argument (var 1)) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
          (correction (var 0) (var 5) (var 6) (var 7)))) :=
  closeUniv 8 (.impI (original_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalCompactInterval
