import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorRecomposition
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialProductTruncation

/-!
# The degree-truncated Barnes value polynomial

Multiply the actual centered head by the finite exponential
polynomial and retain just the requested degree. The original
central exponential is a fixed scalar name. This construction
continues to work at zeros of the centered head.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData base_regular head incrementF incrementData)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (evaluate ofGaussian qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (canonicalCoefficients)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianEuclideanDistanceName (fraction)
open RationalArgmin (rationalLE)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "P" => GaussianBarnesCanonicalCenteredProductRate.nameF
local notation "pd" => GaussianBarnesCanonicalCenteredProductRate.data
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

def headPolynomial (z R B : PTm n) : PTm n :=
  GaussianBarnesCanonicalCenteredHead.polynomial z B (initial R)

def headDegree (R : PTm n) : PTm n := GaussianBarnesCanonicalHeadPolynomial.degree (initial R)

def polynomial (z R B p N m : PTm n) : PTm n :=
  GaussianRationalPolynomialExponentialProductTruncation.polynomial (headPolynomial z R B) p (headDegree R) N m

abbrev nameF : PR 2 := multiplyF E C

def data (z h R B p N m : PTm n) : PTm n :=
  multiplyData E C (baseData z R B) (evaluate (polynomial z R B p N m) (ofGaussian h B))

def tailNumerator (z R B A L H m : PTm n) : PTm n :=
  U E (baseData z R B)*((A*pw (num 3) L)*pw H (succ m))

theorem gather_constants (z h R B v : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent (P C) nameF (pd C z h R B v)
      (multiplyData E C (baseData z R B) (qmul (head z h R B) v)) := by
  let a := head z h R B
  let x := baseData z R B
  let q := qmul a v
  have ha := constant_regular (Γ := Γ) a
  have hx := base_regular z R B hz
  have hv := constant_regular (Γ := Γ) v
  have hq := constant_regular (Γ := Γ) q
  have split := GaussianNameRingLaws.multiply_associative C E C a x v ha hx hv
  have swap := GaussianNameRingLaws.multiply_commutative C E a x ha hx
  have moved := multiply_cross (multiplyF C E) (multiplyF E C) C C
    (multiplyData C E a x) (multiplyData E C x a) v v
    (multiply_fast _ _ _ _ ha hx) (multiply_fast _ _ _ _ hx ha) hv hv swap (cross_refl _ _ hv)
  have grouped := GaussianNameRingLaws.multiply_associative E C C x a v hx ha hv
  have literal := GaussianGammaDigammaTwoShiftNamedSize.constant_product (Γ := Γ) a v q (.eqRefl _)
  have collapsed := multiply_cross E E (multiplyF C C) C x x (multiplyData C C a v) q
    hx hx (multiply_fast _ _ _ _ ha hv) hq (cross_refl _ _ hx) literal
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ moved (cross_trans _ _ _ _ _ _ grouped collapsed))

private theorem constant_rate (a b A D : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] distanceBounded a b A D) : Γ ⊢[PRAAx] independentRate C C a b A D := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hD : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ, sh, Fm.shift, Syn.shift] using hd.shift.shift
  have d : Δ ⊢[PRAAx] distanceBounded (sh a) (sh b) (sh A) (sh D) := by
    simpa [Δ, sh, Fm.shift, Syn.shift] using hr.shift.shift
  have fit : Δ ⊢[PRAAx] le (sh A*rateDenominator (sh D) p q) (rateNumerator (sh A) (sh D) p q*sh D) :=
    le_of_eq_add (d := sh D*sh D*(unit p+unit q)) (by unfold rateNumerator rateDenominator; ipra_ring)
  have radius := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hD
    (GaussianNamedInverseRate.denominator_positive _ _ _ hD) fit d
  simpa only [independentRate, Syn.shift, Δ, sh, p, q] using
    GaussianRationalDistanceOrder.distance_congr (constant_at p (sh a)).eqSymm (constant_at q (sh b)).eqSymm
      (.eqRefl _) (.eqRefl _) radius

theorem scaled_rate (z R B a b A D : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hd : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] distanceBounded a b A D) :
    Γ ⊢[PRAAx] independentRate nameF nameF (multiplyData E C (baseData z R B) a)
      (multiplyData E C (baseData z R B) b) (U E (baseData z R B)*A) D := by
  let x := baseData z R B
  have he := base_regular z R B hz
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have raw := GaussianNamedMultiplyRate.independent_rate E C E C x a x b zero one A D (U C a) (U E x)
    (le_refl one) hd he ha he hb (all_samples_bounded C a ha) (all_samples_bounded E x he)
    (GaussianNamedDifferenceRate.self_rate E x he) (constant_rate a b A D hd hr)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw

def error (z R B A L H m J D K : PTm n) : PTm n :=
  GaussianBarnesCanonicalCenteredProductRate.gain z R B*
    GaussianBarnesCanonicalTaylorRecomposition.error J D m L H B K+D*tailNumerator z R B A L H m

theorem rate (z h R B H p N m L A J D K : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hs : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialRecomposition.input p N m (ofGaussian h B) H B L)
    (hc : Γ ⊢[PRAAx] canonicalCoefficients p)
    (ha : Γ ⊢[PRAAx] rationalLE (coefficientNorm (headPolynomial z R B)) (fraction A one))
    (hd : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le J (K*D))
    (hr : Γ ⊢[PRAAx] independentRate incrementF C (incrementData z h R B) (evaluate p (ofGaussian h B)) J D) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (add z h) R B) (data z h R B p N m)
      (error z R B A L H m J D K) (GaussianBarnesCanonicalTaylorRecomposition.denominator D m B) := by
  let w := ofGaussian h B
  let v := GaussianRationalPolynomialExponentialRecomposition.value p N m w
  let x := baseData z R B
  let b := qmul (head z h R B) v
  let y := multiplyData E C x b
  let j := tailNumerator z R B A L H m
  let e := pw B (succ m)
  let d := GaussianBarnesCanonicalTaylorRecomposition.denominator D m B
  have hB := hs.andE₂.andE₂.andE₂.andE₁
  have he : Γ ⊢[PRAAx] le one e := GaussianFactorBudget.power_positive B (succ m) hB
  have hden : Γ ⊢[PRAAx] le one d := positive_product D e hd he
  have aprox := GaussianBarnesCanonicalTaylorRecomposition.rate z h R B H p N m L J D K hz hw hs hc hd hk hr
  have pre := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hden aprox
    (cross_refl _ _ (GaussianBarnesCanonicalValue.regular (add z h) R B hw))
    (cross_symm _ _ _ _ (gather_constants z h R B v hz))
  have hP := GaussianBarnesCanonicalCenteredHead.polynomial_length (Γ := Γ) z B (initial R)
  have tail := GaussianRationalPolynomialExponentialProductTruncation.tail (headPolynomial z R B)
    p (headDegree R) N m w H B A L hP hs.andE₁ hc hs.andE₂.andE₂.andE₁ hB hs.andE₂.andE₂.andE₂.andE₂.andE₁
    hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂ ha hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have final : Γ ⊢[PRAAx] independentRate nameF nameF y (data z h R B p N m) j e :=
    scaled_rate z R B b _ _ e hz he tail
  have adjust : Γ ⊢[PRAAx] le (j*d) ((D*j)*e) :=
    le_of_eq_add (d := zero) (by dsimp [d,GaussianBarnesCanonicalTaylorRecomposition.denominator,
      GaussianRationalPolynomialExponentialRecomposition.denominator,leadingDenominator]; ipra_ring)
  exact GaussianNamedRateComposition.same_denominator V nameF nameF (vd (add z h) R B) y
    (data z h R B p N m) _ d _ hden pre
    (GaussianNamedRateRadius.weaken _ _ _ _ j e (D*j) d he hden adjust final)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProduct
