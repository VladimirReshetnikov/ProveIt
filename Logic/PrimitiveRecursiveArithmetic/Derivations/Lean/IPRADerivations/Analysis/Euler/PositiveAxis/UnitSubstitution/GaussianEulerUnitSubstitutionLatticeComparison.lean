import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionLatticeRows
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionFloorWidths
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSumTotalDistance
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSumWeightReplacement
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarDifferenceEmbedding

/-!
# The finite original decay-image density versus a separate unit lattice

The fine lattice and the original affine time grid use independent
counts, denominators and kernel precisions. Actual integer cuts group
the original unit rows. An exact width-replacement bound then restores
the signed original decay cells and the original density sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeComparison

open_ipra
open GaussianEulerUnitSubstitutionLatticeGeometry (source start count cuts_source denominator_positive)
open GaussianEulerUnitSubstitutionLatticeRows (latticeData powerData anchorNumerator anchorDenominator anchor_denominator_positive)
open GaussianEulerUnitSubstitutionFloorCuts (cutF cut data)
open GaussianEulerUnitDecayInput (clock)
open GaussianEulerUnitSubstitutionImageGrid (node)
open GaussianEulerUnitSubstitutionReversedDensity (coarsePowerBody leftIndex rightIndex)
open GaussianEulerUnitSubstitutionReversedWeights (widthBody)
open GaussianPartitionedFiniteSumWeightReplacement (rowSource)
open GaussianPartitionedFiniteSumDistance (blockLength)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def widthNumerator (k E T M : PTm n) : PTm n := two*M+two*unit (clock k E T)
def widthDenominator (k E T M : PTm n) : PTm n := M*unit (clock k E T)
def numerator (k q N R C E T M : PTm n) : PTm n :=
  anchorNumerator k q N R C E T M*widthDenominator k E T M+
    N*(majorant R E T*widthNumerator k E T M)*anchorDenominator k q N E T M
def denominator (k q N E T M : PTm n) : PTm n :=
  anchorDenominator k q N E T M*widthDenominator k E T M

ipra_subst widthNumerator
ipra_subst widthDenominator

theorem width_denominator_positive (k N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] le one (widthDenominator k E T M) :=
  positive_product _ _ (denominator_positive _ _ _ _ _ _ _ _ _ _ h) (unit_positive _)

theorem original_width_row (i k N z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] bounded (inst2 coarsePowerBody i (powerData k N z B a C E T)) (majorant R E T) one ⋏
      distanceBounded (fraction (blockLength cutF i (data k N a C E T M)) M) (inst2 widthBody i (powerData k N z B a C E T))
        (widthNumerator k E T M) (widthDenominator k E T M) := by
  let p := clock k E T
  let v := monus (cut (succ i) k N a C E T M) (cut i k N a C E T M)
  let X := node (leftIndex N i) p N a C E
  let Y := node (rightIndex N i) p N a C E
  have hs := cuts_source k N z R B a C E T M h
  have hx := GaussianEulerUnitSubstitutionReversedDensity.grid_decay_real (leftIndex N i) p N z R B a C E T h.andE₁
  have hy := GaussianEulerUnitSubstitutionReversedDensity.grid_decay_real (rightIndex N i) p N z R B a C E T h.andE₁
  have hM := denominator_positive _ _ _ _ _ _ _ _ _ _ h
  have hd := width_denominator_positive _ _ _ _ _ _ _ _ _ _ h
  have near := GaussianScalarDifferenceEmbedding.width_distance v M X Y (widthNumerator k E T M)
    (widthDenominator k E T M) hM hd hx hy (GaussianEulerUnitSubstitutionFloorWidths.original_width_error i k N a C E T M hs hi)
  have left := GaussianCompactRiemannName.fraction_congr _ _ _ _
    (GaussianEulerUnitSubstitutionLatticeGeometry.original_width_at i k N a C E T M hs) (.eqRefl M)
  have widthCode := GaussianEulerUnitSubstitutionReversedWeights.width_at i p N z B a C E hi
  exact .andI (GaussianEulerUnitSubstitutionReversedDensity.reversed_power_bound i p N z R B a C E T h.andE₁)
    (distance_congr left.eqSymm widthCode.eqSymm (.eqRefl _) (.eqRefl _) near)

theorem original_width_rows (k N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] rowSource cutF coarsePowerBody widthBody N (data k N a C E T M) (powerData k N z B a C E T)
      M (majorant R E T) (widthNumerator k E T M) (widthDenominator k E T M) := by
  let s (u : PTm n) := Syn.shift u
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s k) (s N) (s z) (s R) (s B) (s a) (s C) (s E) (s T) (s M) :=
    by simpa [Fm.shift,Syn.shift,s] using h.shift
  refine .allI (.impI ?_)
  simpa only [rowSource,GaussianEulerUnitSubstitutionFloorCuts.subst_data,GaussianEulerUnitSubstitutionLatticeRows.subst_powerData,
    GaussianEulerUnitSubstitutionDensity.subst_majorant,subst_widthNumerator,subst_widthDenominator,Syn.shift,s] using
    original_width_row (var 0) (s k) (s N) (s z) (s R) (s B) (s a) (s C) (s E) (s T) (s M) hs.wk Prf.hyp0

theorem add_errors (x y z A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y A B) (g : Γ ⊢[PRAAx] distanceBounded y z C D) : Γ ⊢[PRAAx]
    distanceBounded x z (A*D+C*B) (B*D) := by
  have pos := positive_product _ _ hB hD
  exact distance_triangle_same _ _ _ _ _ _ pos
    (distance_radius_mono _ _ _ _ _ _ hB pos (le_of_eq_add (d := zero) (by ipra_ring)) h)
    (distance_radius_mono _ _ _ _ _ _ hD pos (le_of_eq_add (d := zero) (by ipra_ring)) g)

theorem original_finite_bound (k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] distanceBounded (GaussianEulerUnitKernelLatticeSum.lattice q (count k N a C E T M) z B (start k N a C E T M) M)
      (GaussianEulerUnitSubstitutionDensity.density (clock k E T) N z B a C E)
      (numerator k q N R C E T M) (denominator k q N E T M) := by
  let d := data k N a C E T M
  let y := powerData k N z B a C E T
  have hs := cuts_source k N z R B a C E T M h
  have hM := denominator_positive _ _ _ _ _ _ _ _ _ _ h
  have hp := anchor_denominator_positive k q N z R B a C E T M h
  have hw := width_denominator_positive _ _ _ _ _ _ _ _ _ _ h
  have coarse := GaussianPartitionedFiniteSumTotalDistance.scaled_total_comparison cutF GaussianEulerUnitKernelLatticeSum.body
    coarsePowerBody N d (latticeData k q N z B a C E T M) y (anchorNumerator k q N R C E T M)
    (anchorDenominator k q N E T M) M hp hM (GaussianEulerUnitSubstitutionFloorCuts.original_increasing k N a C E T M hs)
    (GaussianEulerUnitSubstitutionFloorCuts.original_zero k N a C E T M)
    (GaussianEulerUnitSubstitutionLatticeRows.original_block_agreement k q N z R B a C E T M h)
    (GaussianEulerUnitSubstitutionLatticeGeometry.original_count_bound k N a C E T M hs)
  have weights := GaussianPartitionedFiniteSumWeightReplacement.original_finite_replacement cutF coarsePowerBody widthBody
    N d y M (majorant R E T) (widthNumerator k E T M) (widthDenominator k E T M) hM hw
    (original_width_rows k N z R B a C E T M h)
  exact distance_congr (.eqRefl _)
    (GaussianEulerUnitSubstitutionReversedWeights.original_weighted_density (clock k E T) N z B a C E)
    (.eqRefl _) (.eqRefl _) (add_errors _ _ _ _ _ _ _ hp hw coarse weights)

theorem actual_original_unit_lattice_density_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded (GaussianEulerUnitKernelLatticeSum.lattice (var 1)
        (count (var 0) (var 2) (var 6) (var 7) (var 8) (var 9) (var 10))
        (var 3) (var 5) (start (var 0) (var 2) (var 6) (var 7) (var 8) (var 9) (var 10)) (var 10))
      (GaussianEulerUnitSubstitutionDensity.density (clock (var 0) (var 8) (var 9)) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8))
      (numerator (var 0) (var 1) (var 2) (var 4) (var 7) (var 8) (var 9) (var 10))
      (denominator (var 0) (var 1) (var 2) (var 8) (var 9) (var 10))) :=
  closeUniv 11 (.impI (original_finite_bound _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeComparison
