import IPRADerivations.Analysis.GaussianStirlingNativeDuplication
import IPRADerivations.Analysis.GaussianEulerPositiveTimePowerProduct
import IPRADerivations.Analysis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.GaussianNamedGammaHalfShift

/-!
# Rational logarithms at the arguments of duplication

The two positive rational ratios are related by the exact product
law. The harmonic interval at the reciprocal ratio is the pointwise
negative of the original interval because their horizons coincide.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationLogs

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_equivalent negative_sample_error)
open GaussianPositiveRationalLogarithm (logF data source name_regular)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianStirlingNativeDuplication (halfNumerator halfDenominator half_source double_source)
open RationalHarmonicInterval (interval common horizon numerator common_value common_canonical)
open RationalRepresentations (represents_negative)
open Products (fact)
open GammaEulerMesh (factorial_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data

theorem split_product (a b c d e f : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] source e f)
    (rr : Γ ⊢[PRAAx] e*(b*d) ≐ f*(a*c)) :
    Γ ⊢[PRAAx] crossEquivalent H (addF H logF) (hd e f) (addData (hd a b) (data c d)) := by
  have p := GaussianEulerPositiveTimePowerProduct.logarithm_product a b c d (.andI ha hc)
  have hP := GaussianHarmonicLogarithmProduct.product_source a b c d (.andI ha hc)
  have r := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper e f (a*c) (b*d) he hP rr
  have v := cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original e f he)
  have lift := GaussianNamedGammaHalfShift.add_cross logF H logF logF (data a b) (hd a b) (data c d) (data c d)
    (name_regular a b ha) (GaussianHarmonicLogarithmName.name_regular a b ha)
    (name_regular c d hc) (name_regular c d hc)
    (GaussianHarmonicLogarithmName.cross_original a b ha) (cross_refl _ _ (name_regular c d hc))
  exact cross_trans _ _ _ _ _ _ v (cross_trans _ _ _ _ _ _ r (cross_trans _ _ _ _ _ _ p lift))

def halfRatioData (a b : PTm n) : PTm n := data (halfNumerator a b) (two*a)
def logTwoData : PTm n := data two one

theorem half_log (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent H (addF H logF) (hd (halfNumerator a b) (halfDenominator b))
      (addData (hd a b) (halfRatioData a b)) := by
  have hc : Γ ⊢[PRAAx] source (halfNumerator a b) (two*a) :=
    .andI (half_source a b hs).andE₁ (double_source a b hs).andE₁
  exact split_product a b _ _ _ _ hs hc (half_source a b hs) (by unfold halfNumerator halfDenominator; ipra_ring)

theorem double_log (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent H (addF H logF) (hd (two*a) b) (addData (hd a b) (logTwoData : PTm n)) :=
  split_product a b two one (two*a) b hs (.andI (le_succ_self one) (le_refl one)) (double_source a b hs)
    (by ipra_ring)

theorem interval_reverse (a b Q : PTm n) :
    Γ ⊢[PRAAx] interval a b Q ≐ RationalArithmetic.negative (interval b a Q) := by
  let X := horizon a b Q
  let Y := horizon b a Q
  have e : Γ ⊢[PRAAx] X ≐ Y := by unfold X Y horizon; ipra_ring
  have hXY : Γ ⊢[PRAAx] le Y X := le_congr e (.eqRefl _) (le_refl X)
  have q : Γ ⊢[PRAAx] interval a b Q ≐ RationalArithmetic.negative (common b a Q X) := by
    refine RationalFiniteSum.canonical_equal _ _ _ _ _ _ (common_canonical a b Q X)
      (RationalArithmetic.negative_guard _) (common_value a b Q X)
      (represents_negative _ _ _ (common_value b a Q X)) (factorial_positive X) (factorial_positive X) ?_
    apply ZT.derive (u := numerator a b Q X*ZT.ofNat (fact X))
      (v := (-numerator b a Q X)*ZT.ofNat (fact X))
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_neg]
    simp only [numerator,ZT.toZ]
    ring
  exact q.eqTrans (RationalAlgebra.negative_congr (RationalHarmonicInterval.at_common b a Q X hXY))

private theorem sample_reverse (p a b : PTm n) :
    Γ ⊢[PRAAx] ap2 H p (hd a b) ≐ qnegative (ap2 H p (hd b a)) := by
  let Q := GammaEulerConstantName.mesh (GaussianHarmonicLogarithmName.clock p)
  have src := interval_reverse (Γ := Γ) a b Q
  have boxed := RationalGaussianRealPart.embed_congr src
  have lhs := GaussianHarmonicLogarithmName.sample_at (Γ := Γ) p a b
  have rhs := GaussianHarmonicLogarithmName.sample_at (Γ := Γ) p b a
  exact lhs.eqTrans (boxed.eqTrans ((RationalGaussianEmbedding.embed_negative _).eqTrans
    (GaussianInverseBinomialRows.negative_congr rhs.eqSymm)))

set_option maxHeartbeats 1000000 in
theorem harmonic_inverse (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent H (negativeF H) (hd a b) (negativeData (hd b a)) := by
  have hr := GaussianHarmonicLogarithmName.name_regular _ _ (.andI hs.andE₂ hs.andE₁)
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ GaussianNameRingLaws.three
    (GaussianHarmonicLogarithmName.name_regular _ _ hs) (negative_fast _ _ hr) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let x := Syn.shift a
  let y := Syn.shift b
  let p : PTm (n+1) := var 0
  have h : Δ ⊢[PRAAx] source y x := by
    have h : Γ ⊢[PRAAx] source b a := .andI hs.andE₂ hs.andE₁
    simpa only [Δ,x,y,Fm.shift,Syn.shift,GaussianPositiveRationalLogarithm.subst_source] using h.shift
  have e := sample_reverse (Γ := Δ) p x y
  have base := distance_symmetric _ _ _ _ (unit_positive p) (negative_sample_error H (hd y x) p
    (GaussianHarmonicLogarithmName.name_regular y x h))
  have fold := GaussianRationalSyntheticDivision.qzero_add (Γ := Δ) _ (GaussianRationalMetric.qnegative_canonical (ap2 H p (hd y x)))
  have done := distance_congr (fold.eqTrans e.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) base
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Δ,x,y,p,Syn.shift,
    GaussianHarmonicLogarithmName.subst_data,GaussianNameRingLaws.subst_negativeData,GaussianNameRingLaws.three,
    LeanProofs.IPRA.PTm.subst_num,PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using done

set_option maxHeartbeats 1300000 in
theorem rational_inverse (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent logF (negativeF logF) (data a b) (negativeData (data b a)) := by
  have r : Γ ⊢[PRAAx] source b a := .andI hs.andE₂ hs.andE₁
  have moved := cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original b a r)
  have hH := GaussianHarmonicLogarithmName.name_regular b a r
  have hL := name_regular b a r
  have transported := negative_equivalent H logF (hd b a) (data b a) hH hL
    (GaussianNameEquivalence.cross_to_diagonal H logF (hd b a) (data b a) moved)
  exact cross_trans _ _ _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b hs)
    (cross_trans _ _ _ _ _ _ (harmonic_inverse a b hs) transported)

end LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationLogs
