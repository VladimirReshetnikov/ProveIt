import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherQuartic
import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantRationalRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate
import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalFiberRightInverse

/-!
# Summable increment for the original Glaisher logarithm approximants

The actual named residual `(2*N+1)/4 - ((6*N^2+6*N+1)/12)*log((N+1)/N)`
is bounded by `2/N^3` with independent dyadic observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherIncrement

open_ipra
open ComplexLogarithmRemainder (scale oneCode normSq normSq_scale normSq_neg normSq_one)
open GaussianBarnesGlaisherQuartic (fourth weightNumerator weight negativeWeight correction residual
  residualNumerator residualDenominator residual_denominator_positive numeric_power_four)
open GaussianFiniteLogarithmTaylorRemainder (numerator denominator)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLocalLogarithmTaylorRemainder (polynomial)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical represents positive_product
  qadd qmul qzero canonical_unique)
open GaussianRationalMetric (qsub qnegative qnegative_represents qnegative_canonical bounded_of_cleared bounded distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "neg" => ComplexLogarithmRemainder.neg
local notation "logData" => GaussianPositiveRationalLogarithm.data

def cube (N : PTm n) : PTm n := N*N*N
def weightedF : PR 2 := multiplyF constantF logF
def weightedData (N : PTm n) : PTm n := multiplyData constantF logF (negativeWeight N) (logData (succ N) N)
def nameF : PR 2 := addF constantF weightedF
def data (N : PTm n) : PTm n := addData (correction N) (weightedData N)

theorem cube_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (cube N) :=
  positive_product _ _ (positive_product _ _ hN hN) hN

private theorem negative_weight_representation (N : PTm n) : Γ ⊢[PRAAx]
    represents (negativeWeight N) (neg (scale (weightNumerator N) oneCode)) (num 12) :=
  ofGaussian_represents _ _ (zero_lt_succ (num 11))

private theorem negative_weight_eq (N : PTm n) : Γ ⊢[PRAAx] negativeWeight N ≐ qnegative (weight N) :=
  canonical_unique _ _ _ (num 12) (ofGaussian_canonical _ _ (zero_lt_succ (num 11)))
    (qnegative_canonical _) (zero_lt_succ (num 11)) (negative_weight_representation N)
    (qnegative_represents _ _ _ (ofGaussian_represents _ _ (zero_lt_succ (num 11))))

theorem literal_polynomial_cancellation (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qadd (correction N) (qmul (negativeWeight N) (polynomial (num 4) oneCode N)) ≐ residual N := by
  let P := polynomial (num 4) oneCode N
  have hn := (qmul_congr (negative_weight_eq (Γ := Γ) N) (.eqRefl P)).eqTrans
    (GaussianInverseBinomialRows.negative_product (weight N) P).eqSymm
  exact (qadd_congr (.eqRefl _) hn).eqTrans (GaussianBarnesGlaisherQuartic.exact_cancellation N hN)

private theorem native_norm (P : PTm n) : Γ ⊢[PRAAx] normSq (scale P oneCode) ≐ P*P :=
  (normSq_scale P oneCode).eqTrans
    ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))

theorem negative_weight_bound (N : PTm n) : Γ ⊢[PRAAx] bounded (negativeWeight N) (weightNumerator N) (num 12) := by
  refine bounded_of_cleared _ _ _ _ _ (zero_lt_succ (num 11)) (zero_lt_succ (num 11))
    (negative_weight_representation N) (le_congr ?_ (.eqRefl _) (le_refl _))
  exact ((congrMul (.eqRefl _) ((normSq_neg _).eqTrans (native_norm _))).eqTrans (by ipra_ring)).eqSymm

private theorem radius_bound (N : PTm n) :
    Γ ⊢[PRAAx] bounded (negativeWeight N) (weightNumerator N) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (zero_lt_succ (num 11)) (le_refl one)
    (by ipra_le 11*𝔞(weightNumerator N)) (negative_weight_bound N)

theorem residual_bound (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (residual N) qzero one (cube N) := by
  have hd := residual_denominator_positive N hN
  have hc := cube_positive N hN
  have hR := ofGaussian_canonical (Γ := Γ) (scale (residualNumerator N) oneCode) (residualDenominator N) hd
  have h3 : Γ ⊢[PRAAx] le (num 3) (num 3*N) :=
    by ipra_le 3*sl hN
  have hE : Γ ⊢[PRAAx] le (cube N*residualNumerator N) (one*residualDenominator N) := by
    unfold residualNumerator residualDenominator fourth cube
    ipra_le 𝔞(N*N*N)*sl h3 + 127*𝔞(N*N*N)*𝔞 N
  have hs := le_mul_mono hE hE
  have hb : Γ ⊢[PRAAx] bounded (residual N) one (cube N) := by
    refine bounded_of_cleared _ _ _ _ _ hd hc (ofGaussian_represents _ _ hd) ?_
    exact le_congr ((congrMul (.eqRefl _) (native_norm _)).eqTrans (by ipra_ring)).eqSymm (by ipra_ring) hs
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalReconstruction.qsub_zero_right _ hR).eqSymm (.eqRefl _) (.eqRefl _) hb

private theorem ratio_numerator_one : Γ ⊢[PRAAx] numerator one (num 4) ≐ one := by
  unfold numerator
  exact (pw_succ one (num 4)).eqTrans
    ((congrMul (numeric_power_four (Γ := Γ) one).andE₂.andE₂.andE₂ (.eqRefl _)).eqTrans (by unfold fourth; ipra_ring))

private theorem weighted_budget (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] le ((weightNumerator N*numerator one (num 4))*cube N) (one*(num 12*denominator one N (num 4))) := by
  let d := monus N one
  have h1 : Γ ⊢[PRAAx] le one N := le_trans (le_succ_self one) hN
  have hn : Γ ⊢[PRAAx] N ≐ one+d := eq_add_of_le h1
  have h2 : Γ ⊢[PRAAx] le two (one+d) := le_congr (.eqRefl _) hn hN
  have hD : Γ ⊢[PRAAx] le one d := by ipra_le sl h2
  have gap : Γ ⊢[PRAAx] le N (two*d) := by
    exact le_congr hn.eqSymm (.eqRefl _) (by ipra_le sl hD)
  have hNN : Γ ⊢[PRAAx] le N (N*N) := by ipra_le 𝔞 N*sl h1
  have hOne := le_trans h1 hNN
  have hP : Γ ⊢[PRAAx] le (weightNumerator N) (num 24*(N*N)) := by
    unfold weightNumerator
    ipra_le 6*sl hNN + sl hOne + 11*(𝔞 N)^2
  have hG : Γ ⊢[PRAAx] le (num 24*N) (num 60*d) := by ipra_le 24*sl gap + 12*𝔞 d
  have w := mul_le_mul_right (cube N) hP
  have g := mul_le_mul_right (fourth N) hG
  have top : Γ ⊢[PRAAx] le (weightNumerator N*cube N) (num 60*d*fourth N) :=
    le_trans w (le_congr (by unfold cube fourth; ipra_ring) (.eqRefl _) g)
  have eD : Γ ⊢[PRAAx] one*(num 12*denominator one N (num 4)) ≐ num 60*d*fourth N := by
    unfold denominator d
    exact (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _)
      (numeric_power_four (Γ := Γ) N).andE₂.andE₂.andE₂))).eqTrans (by ipra_ring)
  have eN : Γ ⊢[PRAAx] weightNumerator N*cube N ≐ (weightNumerator N*numerator one (num 4))*cube N :=
    ((congrMul (congrMul (.eqRefl _) ratio_numerator_one) (.eqRefl _)).eqTrans (by ipra_ring)).eqSymm
  exact le_congr eN eD.eqSymm top

theorem regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN nameF (data N) :=
  add_fast _ _ _ _ (constant_regular _) (multiply_fast _ _ _ _ (constant_regular _)
    (GaussianPositiveRationalLogarithm.name_regular _ _ (.andI (zero_lt_succ _) hN)))

private theorem weighted_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate weightedF constantF (weightedData N)
      (qmul (negativeWeight N) (polynomial (num 4) oneCode N)) one (cube N) := by
  let F := GaussianBoundedConstantProductName.nameF
  let X := GaussianBoundedConstantProductName.data (n := n)
  let A := weightNumerator N
  let c := negativeWeight N
  let x := logData (succ N) N
  let y := polynomial (num 4) oneCode N
  let d := denominator one N (num 4)
  let a : PTm n := numerator one (num 4)
  have hN' := le_trans (le_succ_self one) hN
  have hs := GaussianRightHalfPlaneLogarithmMercatorHalfDisk.local_source (succ N) zero N zero one
    (GaussianBarnesGlaisherLogarithm.half_disk_source N hN)
  have hd : Γ ⊢[PRAAx] le one d := GaussianFiniteLogarithmTaylorRemainder.denominator_positive one N _ hN'
    (GaussianLocalLogarithmTaylorRemainder.radius_strict _ _ _ hs)
  have h12 : Γ ⊢[PRAAx] le one (num 12) := zero_lt_succ (num 11)
  have hDen := positive_product _ _ h12 hd
  have clock : Γ ⊢[PRAAx] le A (A*num 12) :=
    by ipra_le 𝔞 A*sl h12
  have h := GaussianBoundedConstantRationalRate.original_rate logF constantF A c x y A (num 12) a d h12 hd clock
    (negative_weight_bound N) (GaussianBarnesGlaisherLogarithm.original_logarithm_rate N (num 4) hN)
  have narrow := GaussianNamedRateRadius.weaken (F logF) (F constantF) (X A c x) (X A c y)
    (A*a) (num 12*d) one (cube N) hDen (cube_positive N hN') (weighted_budget N hN) h
  have left := GaussianBoundedConstantProductName.ordinary_product_identity logF A c x
    (.andI (GaussianPositiveRationalLogarithm.name_regular _ _ (.andI (zero_lt_succ _) hN')) (radius_bound N))
  have right := GaussianBoundedConstantProductName.ordinary_product_identity (Γ := Γ) constantF A c y
    (.andI (constant_regular y) (radius_bound N))
  have fullRight := cross_trans (F constantF) (multiplyF constantF constantF) constantF (X A c y)
    (multiplyData constantF constantF c y) (qmul c y) right (GaussianGammaWeierstrassApproximant.constant_product_cross c y)
  exact GaussianNamedRateTransport.transport (F logF) (F constantF) weightedF constantF (X A c x) (X A c y)
    (weightedData N) (qmul c y) one (cube N) (cube_positive N hN') narrow
    (cross_symm _ _ _ _ left) (cross_symm _ _ _ _ fullRight)

theorem increment_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data N) qzero two (cube N) := by
  let c := correction N
  let y := qmul (negativeWeight N) (polynomial (num 4) oneCode N)
  let D := cube N
  let A := leadingNumerator zero one one D
  let B := leadingDenominator one D
  have h1 := le_trans (le_succ_self one) hN
  have hd := cube_positive N h1
  have hb : Γ ⊢[PRAAx] le one B := positive_product _ _ (le_refl one) hd
  have diag := GaussianNamedAddRate.constant_rate (Γ := Γ) c c zero one (le_refl one)
    (GaussianRationalPowerDifference.distance_refl_zero c one (le_refl one))
  have near := GaussianNamedAddRate.independent_rate constantF weightedF constantF constantF
    c (weightedData N) c y zero one one D (le_refl one) hd diag (weighted_rate N hN)
  have collapses := GaussianNamedGammaHalfShift.constant_sum c y (residual N) (literal_polynomial_cancellation N h1)
  have toResidual := GaussianNamedRateTransport.transport nameF (addF constantF constantF) nameF constantF
    (data N) (addData c y) (data N) (residual N) A B hb near
    (cross_refl _ _ (regular N h1)) (cross_symm _ _ _ _ collapses)
  have tail := GaussianNamedAddRate.constant_rate (residual N) qzero one D hd (residual_bound N h1)
  have together := GaussianNamedRateComposition.compose nameF constantF constantF (data N) (residual N) qzero
    A B one D hb hd toResidual tail
  exact GaussianNamedRateRadius.weaken nameF constantF (data N) qzero
    (leadingNumerator A B one D) (leadingDenominator B D) two D (positive_product _ _ hb hd) hd
    (le_of_eq_add (d := zero) (by unfold A B leadingNumerator leadingDenominator; ipra_ring)) together

theorem actual_Glaisher_summable_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ independentRate nameF constantF (data (var 0)) qzero two (cube (var 0))) :=
  closeUniv 1 (.impI (increment_rate _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherIncrement
