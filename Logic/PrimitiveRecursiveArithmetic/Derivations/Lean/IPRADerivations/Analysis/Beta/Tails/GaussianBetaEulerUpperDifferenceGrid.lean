import IPRADerivations.Analysis.Beta.Tails.GaussianBetaEulerTailDifferencePointwise
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactUpperTail
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# The actual upper beta--Euler grid difference has one half-decay majorant

The two original evaluators use exactly the same mesh, row query and
weight. Literal row differences are summed with the checked original
finite sum, then compared with one scaled half-decay quadrature.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaEulerUpperDifferenceGrid

open_ipra
open GaussianEulerUpperPowerCoefficients (source)
open GaussianBetaEulerTailDifferencePointwise (scalarMajorant referenceError difference)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerCompactUpperTail (halfEvaluator scaledF scaled_at scaled_quadrature)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature
  field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scalarBody : PTm 2 := scalarMajorant (field0 (var 1)) (field5 (var 1))
  (field2 (var 1)*field1 (var 1)+field3 (var 1)*var 0) (field4 (var 1)*field1 (var 1))

theorem scalar_body_at (i p M a C E R : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody i (sampleData p M a C E R) ≐ scalarMajorant p R (a*M+C*i) (E*M) := by
  let x := sampleData p M a C E R
  have num := congrAdd (congrMul (field2_at p M a C E R) (field1_at p M a C E R))
    (congrMul (field3_at p M a C E R) (Prf.eqRefl (Γ := Γ) i))
  have den := congrMul (field4_at (Γ := Γ) p M a C E R) (field1_at p M a C E R)
  ipra_congr (scalarMajorant (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [field0_at p M a C E R, field5_at p M a C E R, num, den] using [scalarBody, inst2, x]

theorem majorized_row (i p M a C E z R B N : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a) (h : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le one N) (hRight : Γ ⊢[PRAAx] le (a+C) (E*N)) (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    majorized (inst2 (differenceBody (sampleBody GaussianBetaKernelGridComparison.evaluatorF) (sampleBody GaussianEulerIntegrandName.evaluatorF)) i
      (pairT (sampleData p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
        (sampleData p M a C E (GaussianEulerIntegrandName.fixedData z B))))
      (inst2 scalarBody i (sampleData p M a C E R)) := by
  let u := a*M+C*i
  let v := E*M
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hE hM
  have hle : Γ ⊢[PRAAx] le v u := le_trans (mul_le_mul_right M hea) (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B u v := .andI h (.andI (.andI (le_trans hv hle) hv) hle)
  have within : Γ ⊢[PRAAx] le u (v*N) :=
    le_trans (add_le_add₂ (le_refl (a*M)) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) (le_of_lt hi)))
      (le_congr (by ipra_ring) (by dsimp only [v]; ipra_ring) (mul_le_mul_right M hRight))
  have left := (sample_body_at (Γ := Γ) GaussianBetaKernelGridComparison.evaluatorF i p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N)).eqTrans
    (GaussianBetaKernelGridComparison.row_at p z B u v N)
  have right := sample_body_at (Γ := Γ) GaussianEulerIntegrandName.evaluatorF i p M a C E (GaussianEulerIntegrandName.fixedData z B)
  have point := (difference_body_at _ _ i _ _).eqTrans (qsub_congr left right)
  exact majorized_congr point.eqSymm (scalar_body_at i p M a C E R).eqSymm
    (GaussianBetaEulerTailDifferencePointwise.original_difference_cell_majorized p z R B u v N hs hN within)

theorem reference_row (i p M a C E R : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] distanceBounded
    (inst2 (embedBody scalarBody) i (sampleData p M a C E R))
    (inst2 (sampleBody scaledF) i (sampleData p M a C E (majorant R))) (referenceError R) (unit p) := by
  let u := a*M+C*i
  let v := E*M
  let K := majorant R
  have hv := positive_product (Γ := Γ) _ _ hE hM
  have left : Γ ⊢[PRAAx] inst2 (embedBody scalarBody) i (sampleData p M a C E R) ≐ embed (scalarMajorant p R u v) := by
    simpa only [inst2,embedBody,RationalGaussianEmbedding.subst_embed] using
      RationalGaussianRealPart.embed_congr (scalar_body_at (Γ := Γ) i p M a C E R)
  have right := (sample_body_at (Γ := Γ) scaledF i p M a C E K).eqTrans
    ((scaled_at p (pairT u v) K).eqTrans (qmul_congr (.eqRefl _)
      (GaussianEulerHalfDecayReference.actual_half_evaluator p u v zero)))
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBetaEulerTailDifferencePointwise.scalar_majorant_half_reference_error p R u v hv)

theorem original_grid_bound_from_scaled_half (p M a C E z R B N U V : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a)
    (h : Γ ⊢[PRAAx] source z R B) (hN : Γ ⊢[PRAAx] le one N) (hRight : Γ ⊢[PRAAx] le (a+C) (E*N))
    (hV : Γ ⊢[PRAAx] le one V)
    (hHalf : Γ ⊢[PRAAx] bounded (qmul (radiusPoint (majorant R) one) (quadrature halfEvaluator p M a C E zero)) U V) : Γ ⊢[PRAAx]
    distanceBounded (quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF p M a C E (GaussianEulerIntegrandName.fixedData z B))
      ((C*referenceError R)*V+U*(E*unit p)) ((E*unit p)*V) := by
  let f := sampleBody GaussianBetaKernelGridComparison.evaluatorF
  let g := sampleBody GaussianEulerIntegrandName.evaluatorF
  let X := sampleData p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N)
  let Y := sampleData p M a C E (GaussianEulerIntegrandName.fixedData z B)
  let Z := sampleData p M a C E R
  let W := sampleData p M a C E (majorant R)
  have hm : Γ ⊢[PRAAx] termsMajorized (differenceBody f g) scalarBody M (pairT X Y) Z := by
    have m' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    have ea' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hea.shift
    have h' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
    have n' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have r' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a+Syn.shift C) (Syn.shift E*Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hRight.shift
    refine .allI (.impI ?_)
    simpa only [termsMajorized,X,Y,Z,f,g,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      GaussianBetaKernelGridComparison.subst_sampleDataBeta,GaussianEulerIntegrandName.subst_fixedData] using
      majorized_row (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) m'.wk e'.wk ea'.wk h'.wk n'.wk r'.wk Prf.hyp0
  have er : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody) (sampleBody scaledF) M Z W (referenceError R) (unit p) := by
    have m' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have e' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    refine .allI (.impI ?_)
    simpa only [termsDistance,Z,W,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerWeightedHalfDecay.subst_majorant,GaussianBetaEulerTailDifferencePointwise.subst_referenceError,
      GaussianCoefficientNameBounds.subst_unit] using
      reference_row (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift R) m'.wk e'.wk
  have dist := GaussianCompactScalarMajorant.common_mesh_distance (embedBody scalarBody) (sampleBody scaledF)
    M Z W C E (referenceError R) (unit p) hM hE (unit_positive p) er
  have error := distance_congr (GaussianCompactScalarMajorant.scalar_left_embedding scalarBody M Z C E hE hM).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) dist
  have scaled : Γ ⊢[PRAAx] bounded (quadrature scaledF p M a C E (majorant R)) U V :=
    GaussianRationalReciprocal.bound_congr (scaled_quadrature p M a C E (majorant R)).eqSymm (.eqRefl _) (.eqRefl _) hHalf
  have norm := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ hE (unit_positive p)) hV error scaled
  have major := GaussianCompactScalarMajorant.weighted_majorant (differenceBody f g) scalarBody M (pairT X Y) Z C E hM hE hm
  exact GaussianRationalReciprocal.bound_congr (weighted_difference f g M X Y C E).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalSumMajorant.majorant_bound _ _ _ _ (positive_product _ _ (positive_product _ _ hE (unit_positive p)) hV) major norm)

theorem original_grid_bound_from_half (p M a C E z R B N U V : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) (hea : Γ ⊢[PRAAx] le E a)
    (h : Γ ⊢[PRAAx] source z R B) (hN : Γ ⊢[PRAAx] le one N) (hRight : Γ ⊢[PRAAx] le (a+C) (E*N))
    (hV : Γ ⊢[PRAAx] le one V) (hHalf : Γ ⊢[PRAAx] bounded (quadrature halfEvaluator p M a C E zero) U V) : Γ ⊢[PRAAx]
    distanceBounded (quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF p M a C E (GaussianEulerIntegrandName.fixedData z B))
      ((C*referenceError R)*V+(majorant R*U)*(E*unit p)) ((E*unit p)*V) :=
  original_grid_bound_from_scaled_half p M a C E z R B N (majorant R*U) V hM hE hea h hN hRight hV
    (GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (one_mul V)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hV (radius_bounded (majorant R) one (le_refl one)) hHalf))

theorem original_shared_upper_difference_one_half_decay_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((le one (var 1) ⋏ le one (var 4) ⋏ le (var 4) (var 2)) ⟶ source (var 5) (var 6) (var 7) ⟶
      (le one (var 8) ⋏ le (var 2+var 3) (var 4*var 8)) ⟶
      (le one (var 10) ⋏ bounded (quadrature halfEvaluator (var 0) (var 1) (var 2) (var 3) (var 4) zero) (var 9) (var 10)) ⟶
      distanceBounded (quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4)
        (GaussianBetaKernelGridComparison.sampleDataBeta (var 5) (var 7) (var 8)))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (GaussianEulerIntegrandName.fixedData (var 5) (var 7)))
        ((var 3*referenceError (var 6))*var 10+(majorant (var 6)*var 9)*(var 4*unit (var 0))) ((var 4*unit (var 0))*var 10)) :=
  closeUniv 11 (.impI (.impI (.impI (.impI (original_grid_bound_from_half _ _ _ _ _ _ _ _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂.andE₁ hyp2.wk.andE₂.andE₂ hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianBetaEulerUpperDifferenceGrid
