import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareComparison
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth

/-!
# The actual corrected quadratic quadrature is the mapped block sum

The original fine weight times the computed block multiplicity is the
original quadratic cell width. Existing finite sum multiplication and
the actual corrected-cell identity therefore bind the entire computed
block sum to the original corrected PR3 quadrature. The Euler endpoint
discharges the compact source internally. Zero width uses positive
independent counts, rather than pretending that W*N^2 is positive.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareCorrectedComparison

open_ipra
open GaussianRationalQuadratureSquarePartition (source lowerNumerator widthNumerator intervalDenominator fineCount cellCap cutData cutF cutGap)
open GaussianRationalQuadratureSquareComparison (fineData coarseData coarseSum squareSum rowNumerator rowDenominator)
open GaussianRationalQuadratureSquareJacobian (pullF correctedF correctedData)
open GaussianPartitionedFiniteSumDistance (coarseBody)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply termsEqual)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem weighted_gap (i N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    qmul (weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C)) (naturalPoint (cutGap i N c a C)) ≐
      GaussianRationalQuadratureSquareCells.cellWidth i N c d a C E := by
  let D := GaussianRationalQuadratureSquareCells.denominator d E N
  have hd : Γ ⊢[PRAAx] le one D := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  exact (qmul_congr (GaussianRationalQuadratureSquarePartition.fine_weight N c d a C E hs) (.eqRefl _)).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product one D (cutGap i N c a C) one hd (le_refl one)).eqTrans
      ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)).eqTrans
        (GaussianRationalQuadratureSquarePartition.cut_gap_cell_width i N c d a C E)))

theorem weighted_coarse_row (F : PR 3) (i p N c d a C E x : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    qmul (weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C))
      (inst2 (coarseBody cutF (sampleBody (pullF F))) i (pairT (cutData N c a C) (coarseData p N c d a C E x))) ≐
      qmul (weight C E N) (ap3 (correctedF F) p (GaussianCompactRiemannName.grid i N a C E) (correctedData N c d C E x)) := by
  let w := weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C)
  let r := inst2 (sampleBody (pullF F)) i (coarseData p N c d a C E x)
  have first := qmul_congr (Γ := Γ) (.eqRefl w) (GaussianPartitionedFiniteSumDistance.coarse_at cutF (sampleBody (pullF F)) i (cutData N c a C) (coarseData p N c d a C E x))
  have nat := qmul_congr (Γ := Γ) (.eqRefl w) (GaussianRationalNaturalScale.natScale_as_product (cutGap i N c a C) r)
  have regroup := (GaussianReciprocalHorner.qmul_associative (Γ := Γ) w (naturalPoint (cutGap i N c a C)) r).eqSymm
  have actual := qmul_congr (weighted_gap i N c d a C E hs) (GaussianRationalQuadratureSquareJacobian.actual_mapped_row F i p N c d a C E x)
  exact first.eqTrans (nat.eqTrans (regroup.eqTrans (actual.eqTrans
    (GaussianRationalQuadratureSquareJacobian.actual_corrected_cell F i p N c d a C E x hs.andE₂.andE₂.andE₂).eqSymm)))

theorem weighted_body_row (F : PR 3) (i p N c d a C E x : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    inst2 (multiplyBody (coarseBody cutF (sampleBody (pullF F)))) i
      (pairT (weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C)) (pairT (cutData N c a C) (coarseData p N c d a C E x))) ≐
    inst2 (multiplyBody (sampleBody (correctedF F))) i (pairT (weight C E N) (sampleData p N a C E (correctedData N c d C E x))) :=
  (multiply_body_at _ _ _ _).eqTrans ((weighted_coarse_row F i p N c d a C E x hs).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianCompactRiemannName.sample_body_at (correctedF F) i p N a C E _).eqSymm).eqTrans
      (multiply_body_at _ _ _ _).eqSymm))

/-- Exact algebra on the same actual finite programs, without a new
recursor or a supplied block-integral identity. -/
theorem original_sum_identity (F : PR 3) (p N c d a C E x : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    squareSum F p N c d a C E x ≐ quadrature (correctedF F) p N a C E (correctedData N c d C E x) := by
  let f := coarseBody cutF (sampleBody (pullF F))
  let g := sampleBody (correctedF F)
  let w := weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C)
  let v := weight C E N
  let y := pairT (cutData N c a C) (coarseData p N c d a C E x)
  let z := sampleData p N a C E (correctedData N c d C E x)
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have rows : Γ ⊢[PRAAx] termsEqual (multiplyBody f) (multiplyBody g) N (pairT w y) (pairT v z) := by
    refine .allI (.impI ?_)
    simpa only [termsEqual,f,g,w,v,y,z,GaussianRationalRiemannRefinement.subst_weight,
      GaussianRationalQuadratureSquarePartition.subst_widthNumerator,GaussianRationalQuadratureSquarePartition.subst_intervalDenominator,
      GaussianRationalQuadratureSquarePartition.subst_fineCount,GaussianRationalQuadratureSquarePartition.subst_cutData,
      GaussianRationalQuadratureSquareComparison.subst_coarseData,GaussianCompactRiemannName.subst_sampleData,
      GaussianRationalQuadratureSquareJacobian.subst_correctedData,subst_pairT,Syn.shift] using
        weighted_body_row F (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x) ss.wk
  exact (sum_multiply f w N y).eqSymm.eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows).eqTrans (sum_multiply g v N z))

theorem original_finite_corrected_comparison (F : PR 3) (p N c d a C E L T x : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianRationalQuadratureSquareComparison.source F N c d a C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p (fineCount N c a C) (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) x)
      (quadrature (correctedF F) p N a C E (correctedData N c d C E x))
      (cellCap c a C*rowNumerator p N c d a C E L) (intervalDenominator d E*rowDenominator p N d E) :=
  distance_congr (.eqRefl _) (original_sum_identity F p N c d a C E x hs.andE₁) (.eqRefl _) (.eqRefl _)
    (GaussianRationalQuadratureSquareComparison.original_finite_comparison F p N c d a C E L T x hs)

def eulerSource (z R B N c d a C E T : PTm n) : Fm PTm n := source c d a C E N ⋏
  GaussianEulerCompactAdditivity.intervalSource z R B (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E) T
ipra_subst eulerSource

/-- The actual Euler client supplies every analytic modulus internally.
The endpoint assumes only its original input disk and numerical geometry. -/
theorem original_Euler_finite_comparison (p z R B N c d a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] eulerSource z R B N c d a C E T) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF p (fineCount N c a C) (lowerNumerator c a) (widthNumerator c a C)
        (intervalDenominator d E) (GaussianEulerIntegrandName.fixedData z B))
      (quadrature (correctedF GaussianEulerIntegrandName.evaluatorF) p N a C E (correctedData N c d C E (GaussianEulerIntegrandName.fixedData z B)))
      (cellCap c a C*rowNumerator p N c d a C E (GaussianEulerCompactModulus.lipschitz R (intervalDenominator d E) T))
      (intervalDenominator d E*rowDenominator p N d E) :=
  original_finite_corrected_comparison _ _ _ _ _ _ _ _ _ _ _
    (.andI hs.andE₁ (GaussianEulerCompactAdditivity.compact_input z R B _ _ _ T hs.andE₂))

/-- At zero width the two actual quadratures are exactly zero. Their
counts remain independently positive; the strict formula W*N^2 is unused. -/
theorem original_zero_width (F : PR 3) (p M N c d a E x : PTm n)
    (hd : Γ ⊢[PRAAx] le one d) (hE : Γ ⊢[PRAAx] le one E) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    quadrature F p M (lowerNumerator c a) (widthNumerator c a zero) (intervalDenominator d E) x ≐
      quadrature (correctedF F) p N a zero E (correctedData N c d zero E x) := by
  have hD := positive_product _ _ (positive_product _ _ hd hE) hE
  have w : Γ ⊢[PRAAx] quadrature F p M (lowerNumerator c a) (widthNumerator c a zero) (intervalDenominator d E) x ≐
      quadrature F p M (lowerNumerator c a) zero (intervalDenominator d E) x := by
    simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (quadrature F (Syn.shift p) (Syn.shift M) (Syn.shift (lowerNumerator c a)) (var 0) (Syn.shift (intervalDenominator d E)) (Syn.shift x))
        (GaussianRationalQuadratureSquarePartition.zero_width c a)
  exact w.eqTrans ((GaussianCompactZeroWidth.quadrature_zero F p M _ _ _ hD hM).eqTrans
    (GaussianCompactZeroWidth.quadrature_zero (correctedF F) p N a E (correctedData N c d zero E x) hE hN).eqSymm)

theorem actual_original_Euler_quadratic_finite_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (eulerSource (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (fineCount (var 4) (var 5) (var 7) (var 8))
          (lowerNumerator (var 5) (var 7)) (widthNumerator (var 5) (var 7) (var 8)) (intervalDenominator (var 6) (var 9))
          (GaussianEulerIntegrandName.fixedData (var 1) (var 3)))
        (quadrature (correctedF GaussianEulerIntegrandName.evaluatorF) (var 0) (var 4) (var 7) (var 8) (var 9)
          (correctedData (var 4) (var 5) (var 6) (var 8) (var 9) (GaussianEulerIntegrandName.fixedData (var 1) (var 3))))
        (cellCap (var 5) (var 7) (var 8)*rowNumerator (var 0) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
          (GaussianEulerCompactModulus.lipschitz (var 2) (intervalDenominator (var 6) (var 9)) (var 10)))
        (intervalDenominator (var 6) (var 9)*rowDenominator (var 0) (var 4) (var 6) (var 9))) :=
  closeUniv 11 (.impI (original_Euler_finite_comparison _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquareCorrectedComparison
