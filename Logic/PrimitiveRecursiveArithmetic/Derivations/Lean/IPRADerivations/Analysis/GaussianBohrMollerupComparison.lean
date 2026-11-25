import IPRADerivations.Analysis.GaussianBohrMollerupSqueeze
import IPRADerivations.Analysis.GaussianBohrMollerupPeriod
import IPRADerivations.Analysis.GaussianBohrMollerupLogWindow
import IPRADerivations.Analysis.GaussianBohrMollerupZeroAlgebra

/-!
# Cofinal comparison of two fixed Bohr–Mollerup presentations

The integer-translated increments differ by the same original
difference, after scaling both by the common argument denominator.
Their common logarithmic window supplies a positive rational bound
with an arbitrarily large effective denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianBohrMollerupChords (base translated base_source translated_source scale_cross rescale_from)
open GaussianBohrMollerupPeriod (differenceF differenceData difference_regular difference_data_congr)
open GaussianBohrMollerupPresentation (Presentation argument observe_value laws scaledData)
open GaussianBohrMollerupSqueeze (logData log_regular incrementF incrementData increment_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaRationalWendelBoundary (difference_cross)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF zero_fast negativeF negativeData negative_fast)
open GaussianNamedDifference (nameF data name_regular)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderTransport (transport)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product canonical_unique ofGaussian_canonical ofGaussian_represents represents_congr)
open GaussianRationalNaturalScale (naturalPoint natScale_canonical natScale_represents natScale_as_product)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "L" => productF H

private theorem zero_at_base (P Q : Presentation) (b j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (differenceF P Q) zeroF (differenceData P Q (base b j) b) zero := by
  let A := base b j
  let i := succ j
  have si : Γ ⊢[PRAAx] source i one := .andI (zero_lt_succ _) (le_refl _)
  have he : Γ ⊢[PRAAx] b ≐ b*one := by ipra_ring
  have hP := hp.andE₂.andE₁
  have hQ := hq.andE₂.andE₁
  have resP := rescale_from P A b i one b hp.andE₂.andE₂.andE₂.andE₁ si hb (.eqRefl _) he
  have resQ := rescale_from Q A b i one b hq.andE₂.andE₂.andE₂.andE₁ si hb (.eqRefl _) he
  have change := difference_cross P.nameF P.nameF Q.nameF Q.nameF
    (argument P A b) (argument P i one) (argument Q A b) (argument Q i one)
    (observe_value P A b hP (base_source b j hb)).andE₁ (observe_value P i one hP si).andE₁
    (observe_value Q A b hQ (base_source b j hb)).andE₁ (observe_value Q i one hQ si).andE₁ resP resQ
  exact cross_trans _ _ _ _ _ _ change (GaussianBohrMollerupPeriod.zero_at_integer P Q j hP hQ
    hp.andE₂.andE₂.andE₁ hq.andE₂.andE₂.andE₁ hp.andE₁ hq.andE₁)

theorem increment_difference (P Q : Presentation) (a b j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (incrementF P) (incrementF Q)) (productF (differenceF P Q))
      (data (incrementData P a b j) (incrementData Q a b j)) (productData (differenceF P Q) b (differenceData P Q a b)) := by
  let A := base b j
  let B := translated a b j
  let X := differenceData P Q B b
  let Y := differenceData P Q A b
  let D := differenceF P Q
  let px := argument P B b
  let qx := argument Q B b
  let py := argument P A b
  let qy := argument Q A b
  have hP := hp.andE₂.andE₁
  have hQ := hq.andE₂.andE₁
  have hA := base_source b j s.andE₂
  have hB := translated_source a b j s.andE₂
  have pX := (observe_value P B b hP hB).andE₁
  have qX := (observe_value Q B b hQ hB).andE₁
  have pY := (observe_value P A b hP hA).andE₁
  have qY := (observe_value Q A b hQ hA).andE₁
  have ex := GaussianBohrMollerupDifferenceTransform.exchange
    (productF P.nameF) (productF P.nameF) (productF Q.nameF) (productF Q.nameF)
    (productData P.nameF b px) (productData P.nameF b py)
    (productData Q.nameF b qx) (productData Q.nameF b qy)
    (GaussianNamedNaturalScaleOrder.regular _ _ _ pX) (GaussianNamedNaturalScaleOrder.regular _ _ _ pY)
    (GaussianNamedNaturalScaleOrder.regular _ _ _ qX) (GaussianNamedNaturalScaleOrder.regular _ _ _ qY)
  have unfoldX := GaussianBohrMollerupDifferenceTransform.scaled_difference P.nameF Q.nameF b px qx pX qX
  have unfoldY := GaussianBohrMollerupDifferenceTransform.scaled_difference P.nameF Q.nameF b py qy pY qY
  have scaleX := GaussianNamedNaturalScaleOrder.regular D b X (difference_regular P Q B b hP hQ hB)
  have scaleY := GaussianNamedNaturalScaleOrder.regular D b Y (difference_regular P Q A b hP hQ hA)
  have regX := name_regular (productF P.nameF) (productF Q.nameF) (productData P.nameF b px) (productData Q.nameF b qx)
    (GaussianNamedNaturalScaleOrder.regular _ _ _ pX) (GaussianNamedNaturalScaleOrder.regular _ _ _ qX)
  have regY := name_regular (productF P.nameF) (productF Q.nameF) (productData P.nameF b py) (productData Q.nameF b qy)
    (GaussianNamedNaturalScaleOrder.regular _ _ _ pY) (GaussianNamedNaturalScaleOrder.regular _ _ _ qY)
  have reshape := difference_cross _ _ _ _ _ _ _ _ regX scaleX regY scaleY unfoldX unfoldY
  have zeroY := GaussianGammaAdjacentCutoff.multiply_cross C C D zeroF (naturalPoint b) (naturalPoint b)
    Y zero (constant_regular _) (constant_regular _) (difference_regular P Q A b hP hQ hA) (zero_fast _)
    (cross_refl _ _ (constant_regular _)) (zero_at_base P Q b j hp hq s.andE₂)
  have zeroS := cross_trans _ _ _ _ _ _ zeroY (GaussianBohrMollerupZeroAlgebra.scaled_zero b zero)
  have cut := difference_cross (productF D) (productF D) (productF D) zeroF
    (productData D b X) (productData D b X) (productData D b Y) zero scaleX scaleX scaleY (zero_fast _)
    (cross_refl _ _ scaleX) zeroS
  have collapse := GaussianBohrMollerupZeroAlgebra.subtract_zero (productF D) (productData D b X) zero scaleX
  have periodic := GaussianBohrMollerupPeriod.periodic P Q a b (succ j) hP hQ
    hp.andE₂.andE₂.andE₁ hq.andE₂.andE₂.andE₁ s
  have e := scale_cross D b b X (differenceData P Q a b) (.eqRefl _)
    (difference_regular P Q B b hP hQ hB) (difference_regular P Q a b hP hQ s) periodic
  exact cross_trans _ _ _ _ _ _ ex (cross_trans _ _ _ _ _ _ reshape
    (cross_trans _ _ _ _ _ _ cut (cross_trans _ _ _ _ _ _ collapse e)))

private theorem product_fraction (t c r : PTm n) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] crossEquivalent (productF C) C (productData C t (fraction c r)) (fraction (t*c) r) := by
  have eq := (natScale_as_product (Γ := Γ) t (fraction c r)).eqSymm
  have val : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale t (scale c oneCode)) (scale (t*c) oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring
  have rep := represents_congr (.eqRefl _) val (.eqRefl _)
    (natScale_represents t (fraction c r) (scale c oneCode) r hr (ofGaussian_represents _ _ hr))
  have ready := canonical_unique _ _ _ _ (natScale_canonical t (fraction c r))
    (ofGaussian_canonical _ _ hr) hr rep (ofGaussian_represents _ _ hr)
  exact cross_trans _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_product_cross (naturalPoint t) (fraction c r))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (eq.eqTrans ready))

theorem comparison (P Q : Presentation) (a b j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hq : Γ ⊢[PRAAx] laws Q) (s : Γ ⊢[PRAAx] source a b)
    (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] realOrder (productF (differenceF P Q)) C
      (productData (differenceF P Q) b (differenceData P Q a b)) (fraction (a*(a+b)) (b*j)) := by
  let r := b*j
  let c := a+b
  let t := translated a b j
  let l := logData a r b
  let u := logData a t b
  let d := productData C a (fraction c r)
  let F := incrementF P
  let G := incrementF Q
  let x := incrementData P a b j
  let y := incrementData Q a b j
  have hR := positive_product (Γ := Γ) _ _ s.andE₂ hj
  have hL := log_regular a r b (.andI hR s.andE₂)
  have hU := log_regular a t b (translated_source a b j s.andE₂)
  have hC := GaussianNamedNaturalScaleOrder.regular (Γ := Γ) C a (fraction c r) (constant_regular _)
  have low := GaussianBohrMollerupSqueeze.lower_increment Q a b j hq.andE₂.andE₁ hq.andE₂.andE₂.andE₁
    hq.andE₂.andE₂.andE₂.andE₁ hq.andE₂.andE₂.andE₂.andE₂ s hj
  have high := GaussianBohrMollerupSqueeze.upper_increment P a b j hp.andE₂.andE₁ hp.andE₂.andE₂.andE₁
    hp.andE₂.andE₂.andE₂.andE₁ hp.andE₂.andE₂.andE₂.andE₂ s
  have hx := increment_regular P a b j hp.andE₂.andE₁ s
  have hy := increment_regular Q a b j hq.andE₂.andE₁ s
  have neg := GaussianNamedRealOrderLinear.negative_order L G l y hL hy low
  have first := add_order F L (negativeF G) (negativeF L) x u (negativeData y) (negativeData l) high neg
  have e : Γ ⊢[PRAAx] r+c ≐ t := by dsimp [r,c,t,translated,base]; ipra_ring
  have eq : Γ ⊢[PRAAx] logData a (r+c) b ≐ u := by
    simpa only [logData,GaussianNaturalScaleProductName.subst_productData,
      GaussianHarmonicLogarithmName.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,u] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (logData (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![a,r+c,b]) (σ' := ![a,t,b]) (fun i => by fin_cases i; exact .eqRefl _; exact e; exact .eqRefl _)
  have leftWin : Γ ⊢[PRAAx] crossEquivalent L L u (logData a (r+c) b) :=
    cross_data_congr L L u u u (logData a (r+c) b) (.eqRefl _) eq.eqSymm (cross_refl _ _ hU)
  have oldWin := GaussianBohrMollerupLogWindow.window_order r b c a hR s.andE₂
  have win := transport L L (addF (productF C) L) (addF (productF C) L)
    u (logData a (r+c) b) (addData d l) (addData d l) leftWin
    (cross_refl _ _ (add_fast _ _ _ _ hC hL)) oldWin
  have right := add_order L (addF (productF C) L) (negativeF L) (negativeF L) u (addData d l)
    (negativeData l) (negativeData l) win (order_refl _ _ (negative_fast _ _ hL))
  have second := transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (name_regular _ _ _ _ hU hL))
    (GaussianNamedStrictOrderDifference.sum_sub_right (productF C) L d l hC hL) right
  have joined := GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ first second
  exact transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (increment_difference P Q a b j hp hq s))
    (product_fraction a c r hR) joined

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupComparison
