import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianLogGammaEulerNamedDigamma
import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianLogGammaEulerSampleDigamma
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedSumDifference

/-!
# Freezing the first-order term of the named log-Gamma expansion

The product of the actual named displacement and named C27 digamma at
the base point has a uniform approximation by the first-order term on
two original rational samples. The latter is precisely the rational
step and the C27 series in the product-denominator chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedLogGammaTaylorFrozen

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono_one unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerCommonDenominator (commonImag commonReal common_arguments common_sources left_represents right_represents)
open GaussianLogGammaEulerDigammaContinuity (canonical_fraction_lipschitz)
open GaussianLogGammaEulerNamedDigamma (rationalMap)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianNameBounds (U all_samples_bounded sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_to_diagonal)
open GaussianNamedInverseRate (independentRate rate_at rateDenominator rateNumerator)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator point realNumerator sign)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (canonical_unique positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical qsub_represents)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalValueEquality (commonDen common_den_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "psiF" => GaussianLogGammaEulerNamedDigamma.nameF
local notation "psiData" => GaussianLogGammaEulerNamedDigamma.data
local notation "seriesF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "seriesData" => GaussianLogGammaEulerSampleDigamma.digammaData
local notation "source" => GaussianNamedRightHalfPlaneLift.source
local notation "clock" => GaussianNamedRightHalfPlaneLift.clock

def nameF (f g : PR 2) : PR 2 := multiplyF (diffF g f) (psiF f)

def data (f g : PR 2) (x y M R : PTm n) : PTm n :=
  multiplyData (diffF g f) (psiF f) (diffData y x) (psiData x M R)

def step (q r : PTm n) : PTm n :=
  GaussianLogGammaEulerArgumentIncrement.step (commonReal q r) (commonImag q r) (sign q)
    (commonReal r q) (commonImag r q) (sign r) (commonDen q r)

def frozenF : PR 2 := multiplyF constantF seriesF

def frozenData (q r : PTm n) : PTm n := multiplyData constantF seriesF (step q r) (seriesData q r)

def cost (f : PR 2) (x M R : PTm n) : PTm n := two*U (psiF f) (psiData x M R)+two*R

theorem regular (f g : PR 2) (x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R) :
    Γ ⊢[PRAAx] pointCN (nameF f g) (data f g x y M R) :=
  multiply_fast _ _ _ _ (GaussianNamedDifference.name_regular g f y x hg.andE₁.andE₁ hf.andE₁.andE₁)
    (GaussianLogGammaEulerNamedDigamma.name_regular f x M R hf)

theorem step_eq_original (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K) :
    Γ ⊢[PRAAx] step q r ≐ qsub r q := by
  have hD := common_den_positive (Γ := Γ) q r
  exact canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) hD
    (GaussianLogGammaEulerArgumentIncrement.step_represents _ _ _ _ _ _ _ hD)
    (qsub_represents _ _ _ _ _ hD (right_represents q r S K hr) (left_represents q r R K hq))

private theorem constant_difference (a b : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (diffF constantF constantF) constantF (diffData a b) (qsub a b) :=
  GaussianNamedSumDifference.constant_difference a b (qsub a b) (.eqRefl _)

private theorem difference_frozen_rate (f g : PR 2) (x y s k : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hsk : Γ ⊢[PRAAx] le s k) :
    Γ ⊢[PRAAx] independentRate (diffF g f) constantF (diffData y x) (qsub (ap2 g k y) (ap2 f k x))
      two (unit s) := by
  let q := ap2 f k x
  let r := ap2 g k y
  let D := unit k
  have hD := unit_positive (Γ := Γ) k
  have hd := GaussianNamedDifferenceRate.original_rate g f constantF constantF y x r q one D one D
    (.andI (.andI hD hD) (.andI (.andI hg hf) (.andI (.andI (constant_regular _) (constant_regular _))
      (.andI (GaussianSignedNameExponentialOrder.own_sample_rate g y k hg)
        (GaussianSignedNameExponentialOrder.own_sample_rate f x k hf)))))
  have hs := unit_positive (Γ := Γ) s
  have cap := unit_monotone hsk
  have coarse := GaussianNamedRateRadius.weaken _ _ _ _ _ _ two (unit s)
    (positive_product _ _ hD hD) hs
    (by dsimp only [GaussianNamedDifferenceRate.leadingNumerator, GaussianNamedDifferenceRate.leadingDenominator, D]
        ipra_le (2*Groth.ι (Q.mk Γ (unit k)))*sl cap) hd
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ two (unit s) hs coarse
    (cross_refl _ _ (GaussianNamedDifference.name_regular _ _ _ _ hg hf))
    (cross_symm _ _ _ _ (constant_difference r q))

private theorem constant_sample_bound (a R : PTm n) (h : Γ ⊢[PRAAx] bounded a R one) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound constantF a R := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift a) (Syn.shift R) one := by
    simpa only [Fm.shift, GaussianRationalMetric.subst_bounded, Syn.shift, one,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using h.shift
  exact GaussianRationalReciprocal.bound_congr (constant_at (var 0) (Syn.shift a)).eqSymm (.eqRefl _) (.eqRefl _) hs

private theorem sampled_step_bound (f g : PR 2) (x y M R k : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R) :
    Γ ⊢[PRAAx] bounded (qsub (ap2 g k y) (ap2 f k x)) (two*R) one := by
  have hgR : Γ ⊢[PRAAx] le (U g y) R := hg.andE₂
  have hfR : Γ ⊢[PRAAx] le (U f x) R := hf.andE₂
  have left := bounded_radius_mono_one hgR (sample_bound g y k hg.andE₁.andE₁)
  have right := bounded_radius_mono_one hfR (sample_bound f x k hf.andE₁.andE₁)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) left right)

private theorem zero_rate_cross (F G : PR 2) (x y : PTm n)
    (hr : Γ ⊢[PRAAx] independentRate F G x y zero one) :
    Γ ⊢[PRAAx] crossEquivalent F G x y := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : Δ ⊢[PRAAx] independentRate F G (sh x) (sh y) zero one := by
    simpa only [Δ, sh, Fm.shift, GaussianNamedInverseRate.subst_independentRate, Syn.shift, one,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using hr.shift.shift
  refine .allI (.allI ?_)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) (rate_at F G (sh x) (sh y) zero one (var 1) (var 0) hs)

private theorem common_digamma (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    crossEquivalent seriesF seriesF (seriesData q r) (GaussianLogGammaEulerNamedDigamma.pointData q) := by
  have sc := common_sources q r R S K hq hr
  have hInput : Γ ⊢[PRAAx] GaussianLogGammaEulerSlopeContinuity.input (commonReal q r) (commonDen q r)
      (sign q) (realNumerator q) (denominator q) (sign q) K :=
    .andI sc.andE₁.andE₁ (.andI hq.andE₁.andE₁ (.andI hK (.andI sc.andE₂.andE₂.andE₁ hq.andE₂.andE₁)))
  have args := common_arguments q r R S K hq hr
  have eq := args.andE₁.eqTrans hq.andE₂.andE₂.eqSymm
  have near : Γ ⊢[PRAAx] distanceBounded
      (GaussianLogGammaEulerHead.argument (commonReal q r) (commonImag q r) (commonDen q r) (sign q))
        (point q) zero one :=
    distance_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero (point q) one (le_refl one))
  have rate := canonical_fraction_lipschitz (commonReal q r) (commonImag q r) (commonDen q r) (sign q)
    (realNumerator q) (imagNumerator q) (denominator q) (sign q) K zero one hInput (le_refl one) near
  exact zero_rate_cross _ _ _ _ (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _
    _ (mul_zero _) (.eqRefl _) rate)

theorem frozen_rate (f g : PR 2) (x y M R s k : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (hsk : Γ ⊢[PRAAx] le s k)
    (hk : Γ ⊢[PRAAx] le (clock rationalMap s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f g) frozenF (data f g x y M R) (frozenData (ap2 f k x) (ap2 g k y))
      (cost f x M R) (unit s) := by
  let q := ap2 f k x
  let r := ap2 g k y
  let u := qsub r q
  let v := GaussianLogGammaEulerNamedDigamma.pointData q
  let d := psiData x M R
  let D := unit s
  let L := U (psiF f) d
  let K := two*M
  have hD := unit_positive (Γ := Γ) s
  have hp := GaussianLogGammaEulerNamedDigamma.name_regular f x M R hf
  have hleft := GaussianNamedDifference.name_regular g f y x hg.andE₁.andE₁ hf.andE₁.andE₁
  have hsr := GaussianNamedRightHalfPlaneLift.clock_margin (Γ := Γ) rationalMap s M R
  have hq := GaussianNamedRightHalfPlaneLift.late_certificate f x k M R hf (le_trans hsr hk)
  have hr := GaussianNamedRightHalfPlaneLift.late_certificate g y k M R hg (le_trans hsr hk)
  have hv := GaussianLogGammaEulerDigammaFractionsCofinal.regular (realNumerator q) (imagNumerator q)
    (denominator q) (sign q) hq.andE₁.andE₁
  have rhs := GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R hf hk
  have rigid : Γ ⊢[PRAAx] crossEquivalent seriesF seriesF v
      (GaussianNamedRightHalfPlaneLift.frozenData rationalMap f k x) := by
    have e := GaussianLogGammaEulerNamedDigamma.rational_data_at (Γ := Γ) q
    exact GaussianGammaCompactCutoffAlignment.cross_data_congr seriesF seriesF v v v
      (GaussianNamedRightHalfPlaneLift.frozenData rationalMap f k x) (.eqRefl _) e.eqSymm
      (cross_refl seriesF v hv)
  have slope : Γ ⊢[PRAAx] independentRate (psiF f) seriesF d v one D :=
    GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ one D hD rhs (cross_refl _ _ hp) rigid
  have product := GaussianNamedMultiplyRate.independent_rate (diffF g f) (psiF f) constantF seriesF
    (diffData y x) d u v two D one D L (two*R) hD hD hleft hp (constant_regular u) hv
    (all_samples_bounded _ _ hp) (constant_sample_bound u _ (sampled_step_bound f g x y M R k hf hg))
    (difference_frozen_rate f g x y s k hf.andE₁.andE₁ hg.andE₁.andE₁ hsk) slope
  have reduce := GaussianNamedRateRadius.weaken _ _ _ _
    (GaussianNamedMultiplyRate.leadingNumerator two D one D L (two*R))
    (GaussianNamedMultiplyRate.leadingDenominator D D) (cost f x M R) D (positive_product _ _ hD hD) hD
    (le_of_eq_add (d := zero) (by
      unfold GaussianNamedMultiplyRate.leadingNumerator GaussianNamedMultiplyRate.leadingDenominator cost L
      ipra_ring)) product
  have sameStep := GaussianSignedNameExponentialOrder.constant_equal_cross (step q r) u (step_eq_original q r R R K hq hr)
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ (zero_lt_succ _) hf.andE₁.andE₂.andE₁
  have sameSlope := common_digamma q r R R K hq hr hK
  have comm := common_sources q r R R K hq hr
  have hv' := GaussianLogGammaEulerDigammaFractionsCofinal.regular (commonReal q r) (commonImag q r)
    (commonDen q r) (sign q) comm.andE₁.andE₁
  have exactProduct := multiply_equivalent constantF constantF seriesF seriesF (step q r) u (seriesData q r) v
    (constant_regular _) (constant_regular _) hv' hv (cross_to_diagonal _ _ _ _ sameStep)
    (cross_to_diagonal _ _ _ _ sameSlope)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ (cost f x M R) D hD reduce
    (cross_refl _ _ (regular f g x y M R hf hg)) exactProduct

theorem actual_named_log_Gamma_first_order_frozen_rate_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let x := var 0
       let y := var 1
       let M := var 2
       let R := var 3
       let s := var 4
       let k := var 5
       (source f x M R ⋏ source g y M R) ⟶
       (le s k ⋏ le (clock rationalMap s M R) k) ⟶
       independentRate (nameF f g) frozenF (data f g x y M R)
         (frozenData (ap2 f k x) (ap2 g k y)) (cost f x M R) (unit s)) :=
  closeUniv 6 (.impI (.impI (frozen_rate f g _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedLogGammaTaylorFrozen
