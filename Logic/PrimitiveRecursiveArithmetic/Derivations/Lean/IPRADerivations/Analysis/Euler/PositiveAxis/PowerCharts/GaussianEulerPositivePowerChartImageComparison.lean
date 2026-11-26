import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageRows
import IPRADerivations.Analysis.Integration.GaussianPartitionedFiniteSumTotalDistance
import IPRADerivations.Analysis.Integration.GaussianCompactSafeGridComparison

/-!
# Ordinary quadrature on the exact corrected image interval

The native lattice contains each corrected point exactly. Grouping its
original Euler observations by the relative cuts gives the corrected
chart sum with its literal weights. Independent uniform grids and
observation indices can then be used on the same exact rational panel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartImageCuts (data numeratorBody denominatorBody cutF start count denominator)
open GaussianEulerPositivePowerChartImageLattice (cutData)
open GaussianEulerPositivePowerChartImageWeights (original_lattice_geometry original_block_width)
open GaussianEulerPositivePowerChartImageRows (coarseBody coarseData fineData cost errorDenominator)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianEulerPowerScalingCorrectedQuadrature (source correctedSum correctedCell correctedBody corrected_body_at)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (quadrature sampleBody)
open GaussianPartitionedFiniteSumDistance (blockLength coarse_at)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit_positive)
open GaussianReciprocalHorner (qmul_associative)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem weighted_repeat (a M v : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (fraction one M) (natScale a v) ≐ qmul (fraction a M) v := by
  have f : Γ ⊢[PRAAx] qmul (fraction one M) (naturalPoint a) ≐ fraction a M :=
    (GaussianEulerDampedTimeRate.fraction_product one M a one hM (le_refl one)).eqTrans
      (GaussianEulerPositivePowerChartJacobian.fraction_congr (by ipra_ring) (by ipra_ring))
  exact (qmul_congr (.eqRefl _) (natScale_as_product a v)).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr f (.eqRefl v)))

theorem corrected_weighted_block (p k i z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hi : Γ ⊢[PRAAx] lt i N) (hJ : Γ ⊢[PRAAx] le one J) :
    let x := data k e f d h Q S E T a C N
    let y := cutData N x J
    let v := coarseData p (scaled z f) (B*e) x
    Γ ⊢[PRAAx] inst2 (multiplyBody (GaussianPartitionedFiniteSumDistance.coarseBody cutF coarseBody))
      i (pairT (fraction one (denominator N x J)) (pairT y v)) ≐
      inst2 correctedBody i (GaussianEulerPowerScalingImageQuadrature.payload p k z B e f d h Q S E T a C N) := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let y := cutData N x J
  let v := coarseData p (scaled z f) (B*e) x
  let M := denominator N x J
  let t := blockLength cutF i y
  let s := inst2 coarseBody i v
  have hM : Γ ⊢[PRAAx] le one M := GaussianEulerPositivePowerChartImageLattice.mesh_positive _ _ _ _ hJ
  have entry := multiply_body_at (Γ := Γ) (GaussianPartitionedFiniteSumDistance.coarseBody cutF coarseBody)
    (fraction one M) i (pairT y v)
  have read := qmul_congr (.eqRefl (fraction one M)) (coarse_at (Γ := Γ) cutF coarseBody i y v)
  have factor := weighted_repeat t M s hM
  have cell : Γ ⊢[PRAAx] qmul (fraction t M) s ≐ correctedCell p k i z B e f d h Q S E T a C N :=
    qmul_congr (original_block_width k i e f d h Q S E T a C N J hs.andE₂ hi hJ)
      (GaussianEulerPositivePowerChartImageRows.coarse_body_at p (scaled z f) (B*e) k i e f d h Q S E T a C N)
  exact entry.eqTrans (read.eqTrans (factor.eqTrans (cell.eqTrans
    (corrected_body_at p k i z B e f d h Q S E T a C N).eqSymm)))

theorem corrected_weighted_sum (p k z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hJ : Γ ⊢[PRAAx] le one J) :
    let x := data k e f d h Q S E T a C N
    Γ ⊢[PRAAx] qmul (fraction one (denominator N x J))
      (sum (GaussianPartitionedFiniteSumDistance.coarseBody cutF coarseBody) N
        (pairT (cutData N x J) (coarseData p (scaled z f) (B*e) x))) ≐
      correctedSum p k z B e f d h Q S E T a C N := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let y := pairT (cutData N x J) (coarseData p (scaled z f) (B*e) x)
  let w := fraction one (denominator N x J)
  let body := GaussianPartitionedFiniteSumDistance.coarseBody cutF coarseBody
  let payload := GaussianEulerPowerScalingImageQuadrature.payload p k z B e f d h Q S E T a C N
  refine (sum_multiply body w N y).eqSymm.eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded (multiplyBody body) correctedBody N (pairT w y) payload (.allI (.impI ?_)))
  let sh (u : PTm n) := Syn.shift u
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (sh k) (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S)
      (sh E) (sh T) (sh a) (sh C) (sh N) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerPowerScalingCorrectedQuadrature.subst_source,sh] using hs.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le one (sh J) := by simpa [Fm.shift,Syn.shift,sh] using hJ.shift
  simpa only [x,y,w,payload,Syn.shift,GaussianEulerPositivePowerChartImageCuts.subst_data,
    GaussianEulerPositivePowerChartImageLattice.subst_cutData,GaussianEulerPositivePowerChartImageLattice.subst_meshDenominator,
    GaussianEulerPositivePowerChartImageRows.subst_coarseData,GaussianPositiveRationalLogarithm.subst_fraction,
    subst_pairT,PTm.subst_mul,GaussianEulerPowerScalingImageQuadrature.subst_payload,sh,
    scaled,ComplexLogarithmRemainder.subst_scale,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    corrected_weighted_block (sh p) (sh k) (var 0) (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h)
      (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N) (sh J) ss.wk Prf.hyp0 js.wk

theorem original_lattice_comparison (p q k z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hJ : Γ ⊢[PRAAx] le one J) :
    let x := data k e f d h Q S E T a C N
    let K := count N x J
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF q K (start N x J) K (denominator N x J)
      (fixedData (scaled z f) (B*e))) (correctedSum p k z B e f d h Q S E T a C N)
      ((majorant Q S E T+one)*cost p q k R h Q S E T C N) (errorDenominator p q k h Q E T N) := by
  dsimp only
  let x := data k e f d h Q S E T a C N
  let y := cutData N x J
  let A := start N x J
  let K := count N x J
  let M := denominator N x J
  let H := majorant Q S E T+one
  let U := cost p q k R h Q S E T C N
  let V := errorDenominator p q k h Q E T N
  have hg := original_lattice_geometry k e f d h Q S E T a C N J hs.andE₂ hJ
  have hM : Γ ⊢[PRAAx] le one M := hg.andE₁.andE₂
  have hK : Γ ⊢[PRAAx] le K (H*M) := le_trans (le_add_left K A) hg.andE₂.andE₂
  have hV : Γ ⊢[PRAAx] le one V :=
    positive_product _ _ (positive_product _ _
      (GaussianEulerPositivePowerChartImageRows.cell_denominator_positive k e f d h Q S E T a C N hs.andE₂)
      (unit_positive q)) (unit_positive p)
  have raw := GaussianPartitionedFiniteSumTotalDistance.weighted_total_comparison cutF (sampleBody evaluatorF) coarseBody N y
    (fineData q (scaled z f) (B*e) N x J) (coarseData p (scaled z f) (B*e) x) U V (fraction one M) one M hV hM
    (GaussianEulerPositivePowerChartImageCuts.original_cut_increasing k e f d h Q S E T a C N J hs.andE₂)
    (GaussianEulerPositivePowerChartImageLattice.cut_zero numeratorBody denominatorBody N x J)
    (GaussianEulerPositivePowerChartImageRows.original_block_agreement p q k z R B e f d h Q S E T a C N J hs hJ)
    (GaussianPartitionedFiniteSumTotalDistance.unit_weight_bound M hM)
  have left := GaussianEulerPositivePowerChartImageUniformGrid.quadrature_value evaluatorF q K A M (fixedData (scaled z f) (B*e)) hM
  have right := corrected_weighted_sum p k z R B e f d h Q S E T a C N J hs hJ
  exact distance_congr left.eqSymm right (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ (M*V) (H*U) V (positive_product _ _ hM hV) hV
      (by change Γ ⊢[PRAAx] le ((one*(K*U))*V) ((H*U)*(M*V)); ipra_le 𝔞 U*𝔞 V*sl hK) raw)

def ordinary (r H k z B e f d h Q S E T a C N J : PTm n) : PTm n :=
  let x := data k e f d h Q S E T a C N
  quadrature evaluatorF r H (start N x J) (count N x J) (denominator N x J) (fixedData (scaled z f) (B*e))

theorem lattice_compact_source (k z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hJ : Γ ⊢[PRAAx] le one J) :
    let x := data k e f d h Q S E T a C N
    Γ ⊢[PRAAx] GaussianEulerPositivePowerChartImageCompactModulus.source (scaled z f) R (B*e)
      (start N x J) (count N x J) (denominator N x J) (reciprocalMargin h Q E T) (majorant Q S E T+one) := by
  have hG := GaussianEulerPositivePowerChartImage.margin_positive h Q E T hs.andE₂.andE₁.andE₁.andE₂.andE₁.andE₂
  exact .andI (.andI hs.andE₁.andE₁ (.andI hG hs.andE₁.andE₂))
    (original_lattice_geometry k e f d h Q S E T a C N J hs.andE₂ hJ)

def comparison (p q r H k z R B e f d h Q S E T a C N J : PTm n) : Fm PTm n :=
  let x := data k e f d h Q S E T a C N
  let K := count N x J
  let M := denominator N x J
  let U := majorant Q S E T+one
  let L := GaussianEulerCompactModulus.lipschitz R (reciprocalMargin h Q E T) U
  let V := errorDenominator p q k h Q E T N
  let D := GaussianCompactSafeGridComparison.denominator q r K H M
  let A := GaussianCompactSafeGridComparison.numerator q r K H M L
  let B₀ := U*cost p q k R h Q S E T C N
  distanceBounded (ordinary r H k z B e f d h Q S E T a C N J) (correctedSum p k z B e f d h Q S E T a C N)
    (A*V+B₀*D) (D*V)

/-- The ordinary panel clock and number of cells are independently chosen.
The error includes the original two row clocks and the full chart mesh. -/
theorem original_independent_comparison (p q r H k z R B e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hJ : Γ ⊢[PRAAx] le one J) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] comparison p q r H k z R B e f d h Q S E T a C N J := by
  unfold comparison
  dsimp only
  let x := data k e f d h Q S E T a C N
  let K := count N x J
  let M := denominator N x J
  let G := reciprocalMargin h Q E T
  let U := majorant Q S E T+one
  let L := GaussianEulerCompactModulus.lipschitz R G U
  let V := errorDenominator p q k h Q E T N
  let D := GaussianCompactSafeGridComparison.denominator q r K H M
  have hc := lattice_compact_source k z R B e f d h Q S E T a C N J hs hJ
  have hM : Γ ⊢[PRAAx] le one M := hc.andE₂.andE₁.andE₂
  have hD : Γ ⊢[PRAAx] le one D := GaussianCompactSafeGridComparison.denominator_positive q r K H M hM hH
  have hV : Γ ⊢[PRAAx] le one V :=
    positive_product _ _ (positive_product _ _
      (GaussianEulerPositivePowerChartImageRows.cell_denominator_positive k e f d h Q S E T a C N hs.andE₂)
      (unit_positive q)) (unit_positive p)
  have hLip := GaussianEulerPositivePowerChartImageCompactModulus.sampled_modulus (scaled z f) R (B*e) (start N x J) K M G U hc
  have independent := GaussianCompactSafeGridComparison.original_comparison evaluatorF q r K H (start N x J) M L
    (fixedData (scaled z f) (B*e)) hc.andE₂.andE₁.andE₁ hM hH hLip
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hD hV
    (distance_symmetric _ _ _ _ hD independent)
    (original_lattice_comparison p q k z R B e f d h Q S E T a C N J hs hJ)

theorem actual_original_corrected_image_independent_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 20
    ((source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)
      (var 14) (var 15) (var 16) (var 17) (var 18) ⋏ (le one (var 19) ⋏ le one (var 3))) ⟶
      comparison (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15) (var 16) (var 17) (var 18) (var 19)) :=
  closeUniv 20 (.impI (original_independent_comparison _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageComparison
