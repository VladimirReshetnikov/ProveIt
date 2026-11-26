import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareGridDistance
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSumDistance
import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareJacobian

/-!
# Actual uniform-to-quadratic finite quadrature comparison

The actual compact local modulus is applied to each original uniform
fine node and the original mapped coarse time. The finite partition
comparison then supplies the weighted whole-sum estimate. Every local
row contract is derived here; no row or sum comparison is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareComparison

open_ipra
open GaussianRationalQuadratureSquarePartition (lowerNumerator widthNumerator intervalDenominator fineCount cellCap cutData cutF cutGap)
open GaussianRationalQuadratureSquareGridDistance (mappedTime targetGrid)
open GaussianRationalQuadratureSquareJacobian (pullF)
open GaussianRationalQuadratureDilation (pullData)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sampledModulus)
open GaussianPartitionedFiniteSumDistance (blockAgreement blockBound blockLength coarseBody)
open GaussianRationalFiniteSum (sum)
open GaussianRationalRiemannRefinement (termsDistance constantBody weight)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (F : PR 3) (N c d a C E L T x : PTm n) : Fm PTm n :=
  GaussianRationalQuadratureSquarePartition.source c d a C E N ⋏
    GaussianCompactRiemannName.input F (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) L T x
def pointDenominator (N d E : PTm n) : PTm n := intervalDenominator d E*N
def rowNumerator (p N c d a C E L : PTm n) : PTm n := L*cellCap c a C*unit p+two*pointDenominator N d E
def rowDenominator (p N d E : PTm n) : PTm n := pointDenominator N d E*unit p
def fineData (p N c d a C E x : PTm n) : PTm n := sampleData p (fineCount N c a C) (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) x
def coarseData (p N c d a C E x : PTm n) : PTm n := sampleData p N a C E (pullData c d x)
def coarseSum (F : PR 3) (p N c d a C E x : PTm n) : PTm n :=
  sum (coarseBody cutF (sampleBody (pullF F))) N (pairT (cutData N c a C) (coarseData p N c d a C E x))
def squareSum (F : PR 3) (p N c d a C E x : PTm n) : PTm n :=
  qmul (weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C)) (coarseSum F p N c d a C E x)

ipra_subst source
ipra_subst pointDenominator
ipra_subst rowNumerator
ipra_subst rowDenominator
ipra_subst fineData
ipra_subst coarseData
ipra_subst coarseSum
ipra_subst squareSum

theorem point_denominator_positive (F : PR 3) (N c d a C E L T x : PTm n) (hs : Γ ⊢[PRAAx] source F N c d a C E L T x) : Γ ⊢[PRAAx]
    le one (pointDenominator N d E) := positive_product _ _
      (GaussianRationalQuadratureSquareGridDistance.target_denominator_positive c d a C E N hs.andE₁) hs.andE₁.andE₂.andE₂.andE₂.andE₂.andE₂

theorem row_denominator_positive (F : PR 3) (p N c d a C E L T x : PTm n) (hs : Γ ⊢[PRAAx] source F N c d a C E L T x) : Γ ⊢[PRAAx]
    le one (rowDenominator p N d E) := positive_product _ _ (point_denominator_positive F N c d a C E L T x hs) (unit_positive p)

theorem mapped_time_at (i N c d a C E : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalQuadratureSquareCells.timeMap c d (GaussianCompactRiemannName.grid i N a C E) ≐ mappedTime i N c d a C E :=
  congrPairT (congrMul (congrMul (.eqRefl _) (fst_pair _ _)) (fst_pair _ _))
    (congrMul (congrMul (.eqRefl _) (snd_pair _ _)) (snd_pair _ _))

theorem coarse_row_at (F : PR 3) (i p N c d a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody (pullF F)) i (coarseData p N c d a C E x) ≐ ap3 F p (mappedTime i N c d a C E) x :=
  (GaussianRationalQuadratureSquareJacobian.actual_mapped_row F i p N c d a C E x).eqTrans
    (congrAp3 F (.eqRefl _) (mapped_time_at i N c d a C E) (.eqRefl _))

theorem original_row_error (F : PR 3) (i j p N c d a C E L T x : PTm n)
    (hs : Γ ⊢[PRAAx] source F N c d a C E L T x) (hi : Γ ⊢[PRAAx] lt i N) (hj : Γ ⊢[PRAAx] lt j (cutGap i N c a C)) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (offB (sampleBody F)) j (pairT (ap2 cutF i (cutData N c a C)) (fineData p N c d a C E x)))
      (inst2 (sampleBody (pullF F)) i (coarseData p N c d a C E x)) (rowNumerator p N c d a C E L) (rowDenominator p N d E) := by
  have hd := point_denominator_positive F N c d a C E L T x hs
  have raw := GaussianCompactRiemannName.sampled_modulus_at F (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) L x p p
    (targetGrid (ap2 cutF i (cutData N c a C)+j) N c d a C E) (mappedTime i N c d a C E) (cellCap c a C) (pointDenominator N d E)
    hs.andE₂.andE₂.andE₂.andE₂ hd (GaussianRationalQuadratureSquareGridDistance.target_inside i j N c d a C E hs.andE₁ hi hj)
    (GaussianRationalQuadratureSquareGridDistance.mapped_inside i N c d a C E hs.andE₁ (le_of_lt hi))
    (GaussianRationalQuadratureSquareGridDistance.original_block_distance i j N c d a C E hs.andE₁ hi hj)
  have fine := (GaussianRationalFiniteProduct.offset_at (Γ := Γ) (sampleBody F) (ap2 cutF i (cutData N c a C)) j (fineData p N c d a C E x)).eqTrans
    (GaussianCompactRiemannName.sample_body_at F _ p _ _ _ _ x)
  have numeric := distance_radius_mono _ _ _ _ (rowNumerator p N c d a C E L) (rowDenominator p N d E)
    (denominator_positive _ _ _ hd) (row_denominator_positive F p N c d a C E L T x hs)
    (le_of_eq_add (d := zero) (by unfold rowNumerator rowDenominator rateNumerator rateDenominator; ipra_ring)) raw
  exact distance_congr fine.eqSymm (coarse_row_at F i p N c d a C E x).eqSymm (.eqRefl _) (.eqRefl _) numeric

theorem inner_agreement (F : PR 3) (i p N c d a C E L T x : PTm n)
    (hs : Γ ⊢[PRAAx] source F N c d a C E L T x) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    termsDistance (offB (sampleBody F)) constantBody (cutGap i N c a C)
      (pairT (ap2 cutF i (cutData N c a C)) (fineData p N c d a C E x))
      (inst2 (sampleBody (pullF F)) i (coarseData p N c d a C E x)) (rowNumerator p N c d a C E L) (rowDenominator p N d E) := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] source F (Syn.shift N) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have ii : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hi.shift
  refine .allI (.impI ?_)
  simpa only [termsDistance,GaussianRationalRiemannRefinement.constant_entry,GaussianRationalQuadratureSquarePartition.subst_cutGap,
    GaussianRationalQuadratureSquarePartition.subst_cutData,subst_fineData,subst_coarseData,subst_rowNumerator,subst_rowDenominator,subst_pairT,subst_ap2,subst_inst2,Syn.shift] using
    original_row_error F (Syn.shift i) (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) ss.wk ii.wk Prf.hyp0

theorem original_block_agreement (F : PR 3) (p N c d a C E L T x : PTm n) (hs : Γ ⊢[PRAAx] source F N c d a C E L T x) : Γ ⊢[PRAAx]
    blockAgreement cutF (sampleBody F) (sampleBody (pullF F)) N (cutData N c a C) (fineData p N c d a C E x)
      (coarseData p N c d a C E x) (rowNumerator p N c d a C E L) (rowDenominator p N d E) := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] source F (Syn.shift N) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hs.shift
  refine .allI (.impI ?_)
  simpa only [blockAgreement,blockLength,GaussianRationalQuadratureSquarePartition.cutGap,
    GaussianRationalQuadratureSquarePartition.subst_cutData,subst_fineData,subst_coarseData,subst_rowNumerator,subst_rowDenominator,Syn.shift] using
    inner_agreement F (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift x) ss.wk Prf.hyp0

theorem original_block_bound (N c a C : PTm n) : Γ ⊢[PRAAx] blockBound cutF N (cutData N c a C) (cellCap c a C*N) := by
  refine .allI (.impI ?_)
  simpa only [blockBound,blockLength,GaussianRationalQuadratureSquarePartition.cutGap,
    GaussianRationalQuadratureSquarePartition.subst_cutData,GaussianRationalQuadratureSquarePartition.subst_cellCap,PTm.subst_mul,Syn.shift] using
    GaussianRationalQuadratureSquarePartition.cut_gap_bound (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift c) (Syn.shift a) (Syn.shift C) Prf.hyp0

/-- A genuine checked finite comparison at the actual uniform mesh.
Every local agreement premise is discharged by the original compact input. -/
theorem original_finite_comparison (F : PR 3) (p N c d a C E L T x : PTm n) (hs : Γ ⊢[PRAAx] source F N c d a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (fineCount N c a C) (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) x)
      (squareSum F p N c d a C E x) (cellCap c a C*rowNumerator p N c d a C E L) (intervalDenominator d E*rowDenominator p N d E) := by
  let w := weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C)
  have hd := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₁.andE₂.andE₂.andE₂
  have hr := row_denominator_positive F p N c d a C E L T x hs
  have hf := GaussianRationalQuadratureSquareGridDistance.target_denominator_positive c d a C E N hs.andE₁
  have hw : Γ ⊢[PRAAx] bounded w one (GaussianRationalQuadratureSquareCells.denominator d E N) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalQuadratureSquarePartition.fine_weight N c d a C E hs.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one _ hd).eqSymm (.eqRefl _) (.eqRefl _)
        (GaussianDominantPairAlgebra.radius_bounded one _ hd))
  have raw := GaussianPartitionedFiniteSumDistance.weighted_comparison cutF (sampleBody F) (sampleBody (pullF F)) N (cutData N c a C)
    (fineData p N c d a C E x) (coarseData p N c d a C E x) (rowNumerator p N c d a C E L) (rowDenominator p N d E)
    (cellCap c a C*N) w one (GaussianRationalQuadratureSquareCells.denominator d E N) hr hd
    (GaussianRationalQuadratureSquarePartition.increasing N c a C) (GaussianRationalQuadratureSquarePartition.cut_zero N c a C)
    (original_block_agreement F p N c d a C E L T x hs) (original_block_bound N c a C) hw
  have fine := GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) (sampleBody F) (GaussianRationalQuadratureSquarePartition.cut_last N c a C) (.eqRefl (fineData p N c d a C E x))
  have moved := distance_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) fine) (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd hr) (positive_product _ _ hf hr)
    (le_of_eq_add (d := zero) (by unfold GaussianRationalQuadratureSquareCells.denominator; dsimp only [intervalDenominator]; ipra_ring)) moved

theorem actual_uniform_to_quadratic_finite_comparison_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (quadrature F (var 0) (fineCount (var 1) (var 2) (var 4) (var 5)) (lowerNumerator (var 2) (var 4))
        (widthNumerator (var 2) (var 4) (var 5)) (intervalDenominator (var 3) (var 6)) (var 9))
        (squareSum F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 9))
        (cellCap (var 2) (var 4) (var 5)*rowNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (intervalDenominator (var 3) (var 6)*rowDenominator (var 0) (var 1) (var 3) (var 6))) :=
  closeUniv 10 (.impI (original_finite_comparison F _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareComparison
