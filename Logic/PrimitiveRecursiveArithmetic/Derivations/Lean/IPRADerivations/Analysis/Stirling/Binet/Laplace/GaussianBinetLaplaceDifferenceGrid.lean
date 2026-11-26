import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceDifferencePrefix
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactDifferenceRefinement

/-!
# The original improper Binet difference on a common finite grid

Choose the same physical horizon for both original improper names.
A common refinement of both unchanged compact prefixes approximates
their normalized improper difference with an explicit dyadic cost.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDifferenceGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetFirstFormulaPinning (laplaceStepData)
open GaussianBinetLaplaceDifferencePrefix (shifted_source prefixStepData prefix_step_rate tailDen tail_den_positive)
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianBinetLaplaceOrderedPrefixes (width)
open GaussianBinetLaplaceStrip (evaluatorF fixedData compact_input)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh precision quadrature)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => evaluatorF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "P" => GaussianBinetLaplaceStrip.nameF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "DName" => GaussianNamedDifference.nameF

def gridCount (p A B D L extra : PTm n) : PTm n :=
  let T := width D L
  mesh p (meshGain (radius A B) T) T * mesh p (meshGain (radius (A+D) B) T) T * extra

def gridValue (q N A B D sign L : PTm n) : PTm n :=
  let T := width D L
  qsub (quadrature F q N (one+zero) T one (fixedData A B D sign (radius A B) T zero))
    (quadrature F q N (one+zero) T one (fixedData (A+D) B D sign (radius (A+D) B) T zero))

private theorem improper_to_prefix (p A B D sign L : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hL : Γ ⊢[PRAAx] le one L)
    (budget : Γ ⊢[PRAAx] le (D*unit p) (unit L)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (DName J J) p (laplaceStepData A B D sign))
      (ap2 (DName P P) p (prefixStepData A B D sign L)) (num 4) (unit p) := by
  let U := unit p
  let E := tailDen A L
  let G := tailDen (A+D) L
  have oneE := tail_den_positive A L h.andE₁.andE₁
  have oneG := tail_den_positive (A+D) L (shifted_source A D sign h).andE₁.andE₁
  have e : Γ ⊢[PRAAx] le (D*U) E := le_trans budget
    (le_congr (one_mul _) (.eqRefl _)
      (mul_le_mul_right (unit L) (positive_product (num 12) A (by ipra_le 11) h.andE₁.andE₁)))
  have g : Γ ⊢[PRAAx] le (D*U) G := le_trans budget
    (le_congr (one_mul _) (.eqRefl _)
      (mul_le_mul_right (unit L) (positive_product (num 12) (A+D) (by ipra_le 11)
        (shifted_source A D sign h).andE₁.andE₁)))
  have core := add_le_add₂ (mul_le_mul_right G e) (mul_le_mul_right E g)
  have den := positive_product E G oneE oneG
  have left := diagonal_rate (DName J J) (DName P P) (laplaceStepData A B D sign)
    (prefixStepData A B D sign L) _ _ p den (prefix_step_rate A B D sign L h hL)
  have cleared : Γ ⊢[PRAAx]
      le (((D*G+D*E)*U+two*(E*G))*U) (num 4*(E*G*U)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right U (add_le_add_right (two*(E*G)) core))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ den (unit_positive p)) (unit_positive p)
    cleared left

theorem at_common_grid (p q A B D sign L extra : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hL : Γ ⊢[PRAAx] le one L) (hx : Γ ⊢[PRAAx] le one extra)
    (budget : Γ ⊢[PRAAx] le (D*unit p) (unit L)) (hq : Γ ⊢[PRAAx] le (precision p (width D L)) q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (DName J J) p (laplaceStepData A B D sign))
      (gridValue q (gridCount p A B D L extra) A B D sign L) (num 16) (unit p) := by
  let T := width D L
  let r := radius A B
  let s := radius (A+D) B
  let k := mesh p (meshGain r T) T
  let m := mesh p (meshGain s T) T
  have hT : Γ ⊢[PRAAx] le (zero+T) (one*T) :=
    le_congr (zero_add T).eqSymm (one_mul T).eqSymm (le_refl T)
  have x := compact_input .cofinal A B D sign r T zero zero T one
    (.andI (source_of_right_half_plane A B D sign h) (.andI (le_refl one) hT))
  have y := compact_input .cofinal (A+D) B D sign s T zero zero T one
    (.andI (source_of_right_half_plane (A+D) B D sign (shifted_source A D sign h)) (.andI (le_refl one) hT))
  have km := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p (meshGain r T) T
  have mm := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p (meshGain s T) T
  have ek : Γ ⊢[PRAAx] m*extra*k ≐ gridCount p A B D L extra := by
    change Γ ⊢[PRAAx] m*extra*k ≐ k*m*extra
    ipra_ring
  have em : Γ ⊢[PRAAx] k*extra*m ≐ gridCount p A B D L extra := by
    change Γ ⊢[PRAAx] k*extra*m ≐ k*m*extra
    ipra_ring
  have refined := GaussianCompactDifferenceRefinement.difference_at_refined_grid F F p q
    (gridCount p A B D L extra) (m*extra) (k*extra) (one+zero) T one
    (meshGain r T) (meshGain s T) T (fixedData A B D sign r T zero) (fixedData (A+D) B D sign s T zero)
    x y (positive_product _ _ mm hx) (positive_product _ _ km hx) hq ek em
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (improper_to_prefix p A B D sign L h hL budget) refined)

theorem actual_Binet_unit_difference_at_shared_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 2) (var 4) (var 5) ⋏ (le one (var 6) ⋏ le one (var 7))) ⋏
      (le (var 4*unit (var 0)) (unit (var 6)) ⋏ le (precision (var 0) (width (var 4) (var 6))) (var 1)) ⟶
      distanceBounded (ap2 (DName J J) (var 0) (laplaceStepData (var 2) (var 3) (var 4) (var 5)))
        (gridValue (var 1) (gridCount (var 0) (var 2) (var 3) (var 4) (var 6) (var 7))
          (var 2) (var 3) (var 4) (var 5) (var 6)) (num 16) (unit (var 0))) :=
  closeUniv 8 (.impI (at_common_grid _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDifferenceGrid
