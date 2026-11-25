import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNative
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalProductSign
import IPRADerivations.Analysis.GaussianNamedRealOrderLinear
import IPRADerivations.Analysis.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsCaps

/-!
# Sign of the original Gamma on an encoded negative interval

The signed shift product is a positive rational c/d. Multiplying the
original shift identity by its exact inverse d/c identifies the
sign-adjusted original Gamma with a positive scalar multiple of
Gamma(1+a/b). The positive endpoint floor 1/18 yields a finite
reciprocal lower certificate 1/(18c).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalGammaSign

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianFactorBudget (power_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalProductSign (signUnit signedProduct magnitude fraction_readback uniform_separation)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalPowerAlgebra (qmul_shuffle qmul_commutative)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianStirlingGammaLogarithm (gammaData gammaMargin gammaRealF gamma_regular gamma_real_positive gamma_real_cross)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open RationalArgmin (rationalLE rationalLE_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "G" => gammaF
local notation "gd" => GaussianGammaNegativeIntervalNative.data

def productNumerator (a b N : PTm n) : PTm n := magnitude a b (succ N)*a
def productDenominator (b N : PTm n) : PTm n := pw b (succ N)*b
def lowerDenominator (a b N : PTm n) : PTm n := gammaMargin*productNumerator a b N
def signedF : PR 2 := multiplyF C G
def signedData (a b N : PTm n) : PTm n := multiplyData C G (signUnit (succ N)) (gd a b N)
def inversePoint (a b N : PTm n) : PTm n := fraction (productDenominator b N) (productNumerator a b N)
def terminalData (a b : PTm n) : PTm n := gammaData (b+a) b

@[simp] theorem subst_lowerDenominator {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (lowerDenominator a b N) = lowerDenominator (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [lowerDenominator, productNumerator]

@[simp] theorem subst_signedData {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (signedData a b N) = signedData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [signedData, GaussianGammaNegativeIntervalNative.data, GaussianGammaNegativeIntervalNative.argument,
    GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight]

private theorem denominator_positive (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] le one (productDenominator b N) := by
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  exact positive_product _ _ (power_positive b (succ N) hb) hb

private theorem numerator_positive (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] le one (productNumerator a b N) := by
  let c := productNumerator a b N
  let d := productDenominator b N
  let e := b*b
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have he := positive_product _ _ hb hb
  have hd := denominator_positive a b N h
  have hr := (congrFst (fraction_readback a b N h.andE₁ h.andE₂)).eqTrans (fraction_real_part c d hd)
  have hlo := rationalLE_congr (fraction_real_part one e he) hr (uniform_separation a b N h.andE₁ h.andE₂)
  have cmp := GaussianRationalMetric.comparison_to_cleared _ _ one c e d
    (GaussianEuclideanDistanceName.fraction_represents one e he)
    (GaussianEuclideanDistanceName.fraction_represents c d hd) hlo
  exact GaussianDominantScalarOrder.factor_positive_left c e
    (le_trans hd (le_congr (by ipra_ring) (.eqRefl _) cmp))

private theorem terminal_source (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (b+a) b := by
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  exact .andI (le_trans hb (le_add_right _ _)) hb

private theorem inverse_times_original (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] qmul (inversePoint a b N) (GaussianGammaNegativeIntervalNative.product a b N) ≐ signUnit (succ N) := by
  let c := productNumerator a b N
  let d := productDenominator b N
  let I := inversePoint a b N
  let S := signUnit (succ N)
  let P := GaussianGammaNegativeIntervalNative.product a b N
  have hc := numerator_positive a b N h
  have hd := denominator_positive a b N h
  have e := fraction_readback a b N h.andE₁ h.andE₂
  have prod : Γ ⊢[PRAAx] qmul I (qmul S P) ≐ qone := by
    exact (qmul_congr (.eqRefl _) e).eqTrans
      ((fraction_product d c c d hc hd).eqTrans
        ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (mul_comm _ _)).eqTrans
          (GaussianRationalExponentialTangent.fraction_one (d*c) (positive_product _ _ hd hc))))
  have square : Γ ⊢[PRAAx] qmul S S ≐ qone := GaussianGammaPoleMultiplier.sign_square (succ N)
  have reduce := (qmul_associative S I (qmul S P)).eqSymm.eqTrans
    ((qmul_shuffle S I S P).eqTrans
      ((qmul_congr square (.eqRefl _)).eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_one_right _ (GaussianRationalHorner.qmul_canonical I P)))))
  exact reduce.eqSymm.eqTrans
    ((qmul_congr (.eqRefl S) prod).eqTrans (qmul_one_right S (GaussianRationalReciprocal.power_canonical _ _)))

theorem signed_gamma_identity (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent signedF signedF (signedData a b N)
      (multiplyData C G (inversePoint a b N) (terminalData a b)) := by
  let I := inversePoint a b N
  let P := GaussianGammaNegativeIntervalNative.product a b N
  let S := signUnit (succ N)
  let x := gd a b N
  let y := terminalData a b
  have hx := GaussianGammaNegativeIntervalNative.negative_regular a b N h
  have hy := gamma_regular (b+a) b (terminal_source a b h)
  have first := GaussianGammaAdjacentCutoff.multiply_cross C C signedF G I I (multiplyData C G P x) y
    (constant_regular _) (constant_regular _) (multiply_fast _ _ _ _ (constant_regular _) hx) hy
    (cross_refl _ _ (constant_regular _)) (GaussianGammaNegativeIntervalNative.original_product a b N h)
  have merge := GaussianGammaEulerShift.merge_head G I P x hx
  have read := GaussianGammaAdjacentCutoff.multiply_cross C C G G (qmul I P) S x x
    (constant_regular _) (constant_regular _) hx hx
    (constant_data_cross _ _ (inverse_times_original a b N h)) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ read)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ merge) first)

private theorem gamma_margin_positive : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := by
  unfold gammaMargin
  ipra_le 17

private theorem terminal_floor (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] realOrder C G (fraction one gammaMargin) (terminalData a b) := by
  have ht := terminal_source a b h
  have cert := (gamma_real_positive (b+a) b ht).andE₂.andE₂
  exact GaussianNamedRealOrderTransport.transport C C gammaRealF G _ _ _ _
    (constant_data_cross _ _ (GaussianGammaDigammaStep.unit_step_value gammaMargin gamma_margin_positive))
    (cross_symm _ _ _ _ (gamma_real_cross (b+a) b ht)) cert

theorem signed_gamma_source (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source signedF (signedData a b N) (lowerDenominator a b N) := by
  let c := productNumerator a b N
  let d := productDenominator b N
  let L := lowerDenominator a b N
  let I := inversePoint a b N
  let t := fraction (one : PTm n) gammaMargin
  let y := terminalData a b
  have hc := numerator_positive a b N h
  have hd := denominator_positive a b N h
  have hm := gamma_margin_positive (Γ := Γ)
  have hL : Γ ⊢[PRAAx] le one L := positive_product _ _ hm hc
  have hy := gamma_regular (b+a) b (terminal_source a b h)
  have p := GaussianNamedRealOrderLinear.fractional_order C G d c t y hc (constant_regular t) hy (terminal_floor a b h)
  have ord := GaussianNamedRealOrderTransport.transport C (multiplyF C C) signedF signedF _ _ _ _
    (cross_symm _ _ _ _ (constant_product_cross I t)) (cross_symm _ _ _ _ (signed_gamma_identity a b N h)) p
  have eq : Γ ⊢[PRAAx] qmul I t ≐ fraction d L :=
    (fraction_product d c one gammaMargin hc hm).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (mul_comm _ _))
  have grow : Γ ⊢[PRAAx] le (L*one) (d*L) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right L hd)
  have low := fractions_order one L d L hL hL grow
  have code := GaussianGammaDigammaStep.unit_step_value L hL
  have lower := constant_order (marginPoint L) (qmul I t)
    (rationalLE_congr (congrFst code) (congrFst eq).eqSymm low)
  have hn := GaussianGammaNegativeIntervalNative.negative_regular a b N h
  exact .andI (multiply_fast _ _ _ _ (constant_regular _) hn) (.andI hL
    (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ lower ord))

theorem strict_sign (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] strictOrder C signedF qzero (signedData a b N) := by
  let L := lowerDenominator a b N
  have hs := signed_gamma_source a b N h
  have hL := hs.andE₂.andE₁
  have hgap : Γ ⊢[PRAAx] lt (L*zero) (one*one) := by
    change Γ ⊢[PRAAx] le (succ (L*zero)) (one*one)
    ipra_le 0
  have s : Γ ⊢[PRAAx] strictOrder C C (fraction zero one) (fraction one L) :=
    .andI (constant_order _ _ (fractions_order zero one one L (le_refl one) hL (le_of_lt hgap)))
      (GaussianStirlingMultiplicativeBoundsCaps.strict_fractions zero one one L (le_refl one) hL hgap)
  have ordered := strict_transport C C C C qzero (fraction zero one) (fraction one L) (marginPoint L)
    (constant_data_cross _ _ (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one)).eqSymm)
    (constant_data_cross _ _ (GaussianGammaDigammaStep.unit_step_value L hL)) s
  exact GaussianNamedStrictOrderDifference.trans_weak _ _ _ _ _ _ ordered hs.andE₂.andE₂

theorem actual_original_negative_interval_Gamma_sign_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶
        (GaussianNamedRightHalfPlane.source signedF (signedData (var 0) (var 1) (var 2))
          (lowerDenominator (var 0) (var 1) (var 2)) ⋏
         strictOrder C signedF qzero (signedData (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.andI (signed_gamma_source _ _ _ Prf.hyp0) (strict_sign _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalGammaSign
