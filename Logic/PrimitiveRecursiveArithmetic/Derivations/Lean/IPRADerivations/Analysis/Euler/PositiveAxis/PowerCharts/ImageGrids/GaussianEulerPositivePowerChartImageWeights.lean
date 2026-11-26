import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImageCuts
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImageCompactModulus
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSumWeightReplacement

/-!
# Exact width and compact bounds for the positive chart lattice
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageWeights

open_ipra
open GaussianEulerPositivePowerChartCorrectedImage (input imageNumerator imageDenominator imageFraction)
open GaussianEulerPositivePowerChartImageCuts (data numeratorBody denominatorBody cutF start count denominator)
open GaussianEulerPositivePowerChartImageLattice (cutData multiplier absolute_below absolute_as_relative)
open GaussianEulerPositivePowerChartImage (reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianEulerPositivePowerChartMeshJacobian (width)
open GaussianPartitionedFiniteSumDistance (blockLength)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open ComplexLogarithmRemainder (scale oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem fraction_difference (A B M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hAB : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] qsub (fraction B M) (fraction A M) ≐ fraction (monus B A) M := by
  let g := scale (monus B A) oneCode
  have er := natEq (eq_add_of_le hAB)
  have G : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRootAlgebra.sub (scale B oneCode) (scale A oneCode)) g := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [g,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps
    · linear_combination er
    · ring
  have actual := GaussianRationalMetric.qsub_represents (fraction B M) (fraction A M) (scale B oneCode) (scale A oneCode) M hM
    (GaussianRationalHorner.ofGaussian_represents _ _ hM) (GaussianRationalHorner.ofGaussian_represents _ _ hM)
  exact GaussianRationalHorner.canonical_unique _ _ g M (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hM) hM
    (GaussianRationalHorner.represents_congr (.eqRefl _) G (.eqRefl _) actual)
    (GaussianRationalHorner.ofGaussian_represents _ _ hM)

theorem original_block_width (k i e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] fraction (blockLength cutF i (cutData N (data k e f d h Q S E T a C N) J))
      (denominator N (data k e f d h Q S E T a C N) J) ≐ width k i e f d h Q S E T a C N := by
  let x := data k e f d h Q S E T a C N
  let d' := cutData N x J
  let A := start N x J
  let M := denominator N x J
  let b := ap2 cutF i d'
  let c := ap2 cutF (succ i) d'
  have hh : Γ ⊢[PRAAx] le b c :=
    GaussianPartitionedFiniteSum.cut_step cutF d' i (GaussianEulerPositivePowerChartImageCuts.original_cut_increasing k e f d h Q S E T a C N J hs)
  have hM : Γ ⊢[PRAAx] le one M := GaussianEulerPositivePowerChartImageLattice.mesh_positive _ _ _ _ hJ
  have length : Γ ⊢[PRAAx] monus (A+c) (A+b) ≐ monus c b :=
    (congrMonus (add_comm A c) (add_comm A b)).eqTrans (monus_add_add c b A)
  have diff := fraction_difference (A+b) (A+c) M hM
    (le_congr (add_comm b A) (add_comm c A) (add_le_add_right A hh))
  have left := (GaussianEulerPositivePowerChartImageCuts.original_lattice_node k i e f d h Q S E T a C N J hs (le_of_lt hi) hJ).eqTrans
    (GaussianEulerPositivePowerChartCorrectedImage.fraction_exact k i e f d h Q S E T a C N hs.andE₁ (le_of_lt hi))
  have right := (GaussianEulerPositivePowerChartImageCuts.original_lattice_node k (succ i) e f d h Q S E T a C N J hs hi hJ).eqTrans
    (GaussianEulerPositivePowerChartCorrectedImage.fraction_exact k (succ i) e f d h Q S E T a C N hs.andE₁ hi)
  exact ((GaussianEulerPositivePowerChartJacobian.fraction_congr length.eqSymm (.eqRefl _)).eqTrans diff.eqSymm).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr right left)

private theorem exact_native_domain (k i e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain
      (GaussianEulerPositivePowerChartImageLattice.absolute numeratorBody denominatorBody i N (data k e f d h Q S E T a C N) J)
      (denominator N (data k e f d h Q S E T a C N) J) (reciprocalMargin h Q E T) (majorant Q S E T+one) := by
  let x := data k e f d h Q S E T a C N
  let F := multiplier denominatorBody i N x J
  let M := denominator N x J
  let A := GaussianEulerPositivePowerChartImageLattice.absolute numeratorBody denominatorBody i N x J
  let U := imageNumerator k i e f d h Q S E T a C N
  let V := imageDenominator k i e f d h Q S E T a C N
  let G := reciprocalMargin h Q E T
  let H := majorant Q S E T+one
  have hd := GaussianEulerPositivePowerChartImageCuts.original_denominators k e f d h Q S E T a C N hs
  have lc := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain k i e f d h Q S E T a C N hs hi
  have pF : Γ ⊢[PRAAx] le one F := GaussianEulerPositivePowerChartImageLattice.multiplier_positive _ _ _ _ _ hd hi hJ
  have pM : Γ ⊢[PRAAx] le one M := GaussianEulerPositivePowerChartImageLattice.mesh_positive _ _ _ _ hJ
  have ea : Γ ⊢[PRAAx] A ≐ U*F := (absolute_below numeratorBody denominatorBody i N x J hi).eqTrans
    (congrMul (GaussianEulerPositivePowerChartImageCuts.numerator_at k i e f d h Q S E T a C N) (.eqRefl _))
  have em : Γ ⊢[PRAAx] M ≐ V*F :=
    (GaussianEulerPositivePowerChartImageLattice.original_multiplier denominatorBody i N x J hd hi).eqTrans
      (congrMul (GaussianEulerPositivePowerChartImageCuts.denominator_at k i e f d h Q S E T a C N) (.eqRefl _))
  have pA : Γ ⊢[PRAAx] le one A := le_congr (.eqRefl _) ea.eqSymm (positive_product _ _ lc.andE₁.andE₁ pF)
  have hlow : Γ ⊢[PRAAx] le M (G*A) := le_congr em.eqSymm
    ((by ipra_ring : Γ ⊢[PRAAx] (G*U)*F ≐ G*(U*F)).eqTrans (congrMul (.eqRefl G) ea.eqSymm))
    (mul_le_mul_right F lc.andE₂.andE₁)
  have hhigh : Γ ⊢[PRAAx] le A (H*M) := le_congr ea.eqSymm
    ((by ipra_ring : Γ ⊢[PRAAx] (H*V)*F ≐ H*(V*F)).eqTrans (congrMul (.eqRefl H) em.eqSymm))
    (mul_le_mul_right F lc.andE₂.andE₂)
  exact .andI (.andI pA pM) (.andI hlow hhigh)

theorem original_lattice_geometry (k e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] GaussianEulerPositivePowerChartImageCompactModulus.geometry
      (start N (data k e f d h Q S E T a C N) J) (count N (data k e f d h Q S E T a C N) J)
      (denominator N (data k e f d h Q S E T a C N) J) (reciprocalMargin h Q E T) (majorant Q S E T+one) := by
  let x := data k e f d h Q S E T a C N
  have hstart := exact_native_domain k zero e f d h Q S E T a C N J hs (zero_le N) hJ
  have hstop := exact_native_domain k N e f d h Q S E T a C N J hs (le_refl N) hJ
  have hd := GaussianEulerPositivePowerChartImageCuts.original_denominators k e f d h Q S E T a C N hs
  have ho := GaussianEulerPositivePowerChartImageCuts.original_ordered k e f d h Q S E T a C N hs
  have e := absolute_as_relative numeratorBody denominatorBody N N x J hd ho (le_refl N)
  exact .andI hstart.andE₁ (.andI hstart.andE₂.andE₁ (le_congr e.eqSymm (.eqRefl _) hstop.andE₂.andE₂))

theorem original_cut_order (k i j e f d h Q S E T a C N J : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] le (ap2 cutF i (cutData N (data k e f d h Q S E T a C N) J))
      (ap2 cutF j (cutData N (data k e f d h Q S E T a C N) J)) := by
  let x := data k e f d h Q S E T a C N
  have hi := le_trans hij hj
  have hd := GaussianEulerPositivePowerChartImageCuts.original_denominators k e f d h Q S E T a C N hs
  have ho := GaussianEulerPositivePowerChartImageCuts.original_ordered k e f d h Q S E T a C N hs
  have h1 := GaussianEulerPositivePowerChartImageLattice.ordered_at numeratorBody denominatorBody i j N x ho hij hj
  have h2 := GaussianEulerPositivePowerChartImageLattice.node_order numeratorBody denominatorBody i j N x J hd hi hj h1
  have h3 := le_congr (absolute_below numeratorBody denominatorBody i N x J hi).eqSymm
    (absolute_below numeratorBody denominatorBody j N x J hj).eqSymm h2
  exact le_congr (GaussianEulerPositivePowerChartImageLattice.cut_at numeratorBody denominatorBody i N x J).eqSymm
    (GaussianEulerPositivePowerChartImageLattice.cut_at numeratorBody denominatorBody j N x J).eqSymm
    (DiophantineNumberTheory.FractionCount.monus_mono (c := start N x J) h3)

theorem fraction_bound_mono (A B M L D : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hD : Γ ⊢[PRAAx] le one D) (hAB : Γ ⊢[PRAAx] le A B) (h : Γ ⊢[PRAAx] bounded (fraction B M) L D) :
    Γ ⊢[PRAAx] bounded (fraction A M) L D := by
  have sq (a : PTm n) : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (scale a oneCode) ≐ a*a := by
    apply deriveNat
    rw [ComplexLogarithmRemainder.normSq_eval]
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
    ipra_simps
    ring
  have old := GaussianRationalMetric.bounded_to_cleared (fraction B M) (scale B oneCode) M L D hM hD
    (GaussianRationalHorner.ofGaussian_represents _ _ hM) h
  have step : Γ ⊢[PRAAx] le ((D*D)*(A*A)) ((D*D)*(B*B)) := by
    ipra_le 𝔞(D*D)*(𝔞 A+𝔞 B)*sl hAB
  have norm := le_congr (congrMul (.eqRefl _) (sq A)).eqSymm (congrMul (.eqRefl _) (sq B)).eqSymm step
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hM hD
    (GaussianRationalHorner.ofGaussian_represents _ _ hM) (le_trans norm old)

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageWeights
