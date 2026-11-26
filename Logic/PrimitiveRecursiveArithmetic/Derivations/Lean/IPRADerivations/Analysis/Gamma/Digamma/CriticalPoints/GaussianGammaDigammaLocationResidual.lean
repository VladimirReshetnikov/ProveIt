import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaDyadicLocation
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaReal
import IPRADerivations.Analysis.Names.Arithmetic.RationalGaussianNameEmbedding

/-!
# Gaussian residual at the primitive recursive digamma location

The selected scalar grid sample is small at the search precision.
A real-axis observation one bit later lifts that scalar estimate to
a Euclidean bound on the original Gaussian name at any query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationResidual

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaDyadicLocation (lower residual_at)
open GaussianGammaDigammaDyadicMesh (clock grid grid_positive)
open GaussianNameEquivalence (cross_at)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianSignedNameExponentialOrder (real_sample_at)
open GaussianStirlingGammaLogarithm (source)
open RationalGaussianEmbedding (scalarZero canonical_axis_roundtrip embed_zero)
open RationalGaussianNameEmbedding (distance_from_radius)
open RationalValueBounds (radius_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "RF" => GaussianGammaDigammaReal.nameF
local notation "rd" => GaussianGammaDigammaReal.data

theorem location_source (p : PTm n) : Γ ⊢[PRAAx] source (lower p) (grid p) :=
  .andI (le_trans (grid_positive p) (le_add_right _ _)) (grid_positive p)

theorem original_residual_at (p q : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 DF q (dd (lower p) (grid p))) qzero
      (num 6*unit q+grid p) (grid p*unit q) := by
  let B := grid p
  let a := lower p
  let t := succ (clock p)
  let V := unit t
  let T := unit q
  let Y := ap2 RF t (rd a B)
  let Z := ap2 DF (clock p) (dd a B)
  have hb := grid_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) t
  have hq := unit_positive (Γ := Γ) q
  have hs := location_source (Γ := Γ) p
  have e := GaussianGammaDigammaReal.original_cross a B hs
  have hBV := positive_product B V hb hv
  have prior : Γ ⊢[PRAAx] distanceBounded Z Y (B+V) (B*V) :=
    cross_at DF RF (dd a B) (rd a B) (clock p) t e
  have scalar := scalar_coordinate_distance Y Z _ _ hBV (distance_symmetric _ _ _ _ hBV prior)
  have small := radius_triangle (fstT Y) (fstT Z) scalarZero _ _ (num 4) B scalar (residual_at p)
  have real := real_sample_at (Γ := Γ) RF (rd a B) t (GaussianGammaDigammaReal.name_real a B)
  have hsmall := positive_product _ _ hBV hb
  have real_residual := distance_congr (canonical_axis_roundtrip Y real.andE₁ real.andE₂) embed_zero
    (.eqRefl _) (.eqRefl _) (distance_from_radius _ _ _ _ hsmall small)
  have hTV := positive_product T V hq hv
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hTV hsmall
    (cross_at DF RF (dd a B) (rd a B) q t e) real_residual
  have hd : Γ ⊢[PRAAx] V ≐ B*two := pw_succ two (clock p)
  have hv' : 𝔞(V)=2*𝔞(B) := by
    have h := natEq hd
    ipra_simps
    linear_combination h
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hTV hsmall)
    (positive_product _ _ hb hq) (by ipra_le 0 using rw [hv']; ring) joined

theorem actual_original_digamma_location_gaussian_residual_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (distanceBounded (ap2 DF (var 1) (dd (lower (var 0)) (grid (var 0)))) qzero
        (num 6*unit (var 1)+grid (var 0)) (grid (var 0)*unit (var 1))) :=
  closeUniv 2 (original_residual_at _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationResidual
