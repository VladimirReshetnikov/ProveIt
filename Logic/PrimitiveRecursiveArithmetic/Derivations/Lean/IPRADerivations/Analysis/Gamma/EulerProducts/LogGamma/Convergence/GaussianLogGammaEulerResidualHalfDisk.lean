import IPRADerivations.Analysis.Logarithm.RightHalfPlane.NearOne.GaussianRightHalfPlaneLogarithmHalfDiskBound
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualCanonicalError

/-!
# The sharp half-disk cutoff for the original Euler residual row

For the row at k, its original offset is z/k. The native disk condition
2R≤k admits that actual offset into the half-disk comparison. Its
canonical logarithm then inherits the original Mercator quadratic bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualHalfDisk

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source rowOffset centered_native linearTerm linear_point)
open GaussianLogGammaEulerResidualCanonicalError (canonicalPoint)
open GaussianLogGammaEulerResidualError (localPoint)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "M" => GaussianLocalLogarithmName.pointF
local notation "md" => GaussianLocalLogarithmName.data

theorem admission (A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (two*R) k) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmMercatorHalfDisk.source (A+k*D) B (D*k) neg (R*D) := by
  have hs := (GaussianLogGammaEulerHead.shifted_source k A D neg h.andE₁).andE₁
  have hd := positive_product D k h.andE₁.andE₂ hk
  have hb : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (rowOffset A B D neg k) (R*D) :=
    le_congr (GaussianRootAlgebra.normSq_equal (centered_native A B D neg k)).eqSymm (.eqRefl _) h.andE₂
  have width : Γ ⊢[PRAAx] le (two*(R*D)) (D*k) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl D) hlarge)
  exact .andI (.andI hs hd) (.andI hb width)

theorem row_equivalent (A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (two*R) k) :
    Γ ⊢[PRAAx] crossEquivalent L M (ld (A+k*D) B (D*k) neg) (md (rowOffset A B D neg k) (R*D) (D*k)) :=
  GaussianRightHalfPlaneLogarithmHalfDiskBound.coincidence (A+k*D) B (D*k) neg (R*D)
    (admission A B D neg R k h hk hlarge)

theorem canonical_sample_error (p A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) (hlarge : Γ ⊢[PRAAx] le (two*R) k) :
    Γ ⊢[PRAAx] distanceBounded (canonicalPoint p A B D neg k) (linearTerm A B D neg k)
      (R*R*unit p+num 3*(k*k)) (k*k*unit p) := by
  let w := rowOffset A B D neg k
  let d := D*k
  let u := unit p
  let x := canonicalPoint p A B D neg k
  let y := localPoint p A B D neg R k
  let z := linearTerm A B D neg k
  have hs := GaussianRightHalfPlaneLogarithmMercatorHalfDisk.local_source (A+k*D) B d neg (R*D)
    (admission A B D neg R k h hk hlarge)
  have hd := positive_product D k h.andE₁.andE₂ hk
  have hp := unit_positive (Γ := Γ) p
  have hh := positive_product _ _ (positive_product _ _ hk hk) hp
  have finite := GaussianLocalLogarithmLinearRemainder.original_linear_remainder p w (R*D) d hs
  have raw := distance_radius_mono _ _ _ _ (R*R*u+k*k) (k*k*u)
    (positive_product _ _ (positive_product _ _ hd hd) hp) hh
    (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) finite
  have lin := distance_congr (.eqRefl _) (linear_point A B D neg k h.andE₁.andE₂ hk) (.eqRefl _) (.eqRefl _) raw
  have near : Γ ⊢[PRAAx] distanceBounded x y (u+u) (u*u) :=
    cross_at L M (ld (A+k*D) B d neg) (md w (R*D) d) p p (row_equivalent A B D neg R k h hk hlarge)
  have uu := positive_product _ _ hp hp
  have total := GaussianRationalPanelTailDistance.triangle x y z (u+u) (u*u) (R*R*u+k*k) (k*k*u) uu hh near lin
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ uu hh) hh
    (le_of_eq_add (d := zero) (by ipra_ring)) total

theorem actual_canonical_Euler_row_half_disk_quadratic_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le (two*var 4) (var 5))) ⟶
        distanceBounded (canonicalPoint (var 6) (var 0) (var 1) (var 2) (var 3) (var 5))
          (linearTerm (var 0) (var 1) (var 2) (var 3) (var 5))
          (var 4*var 4*unit (var 6)+num 3*(var 5*var 5)) (var 5*var 5*unit (var 6))) :=
  closeUniv 7 (.impI (canonical_sample_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualHalfDisk
