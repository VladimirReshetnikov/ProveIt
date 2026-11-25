import IPRADerivations.Analysis.GaussianStirlingWallisRatioRate
import IPRADerivations.Analysis.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.GaussianStirlingLogDuplication

/-!
# Logarithm of the actual positive Wallis ratio near one

For (n=r+1ge 6) the named Wallis ratio has a certified margin
(1/2). Its original positive log reads only the retimed ratio,
and its actual observations approach zero with (O(1/n)) error.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingWallisLogRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingWallisGammaRatio (wallisF wallisData ratioF ratioData wallis_cross)
open GaussianStirlingWallisRatioRate (wallis_rate)
open GaussianStirlingWallisFactor (ratioFactor even_square_positive)
open GaussianStirlingNames (fraction_axis constant_real multiply_real positive_log_real)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedRightHalfPlane (marginPoint threshold)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNameArithmetic (multiply_fast)
open GaussianRationalHorner (qzero ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (qone)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius)
open RationalSupMetric (numeratorOf denominatorOf)
open ComplexLogarithmRemainder (oneCode re)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF

def retimed : PR 2 := retimedF wallisF
def inputData (r x : PTm n) : PTm n := retimedData (wallisData r x) two
def margin : PTm n := two*two
def nameF : PR 2 := GaussianNamedPositiveLogarithm.nameF retimed
def data (r x : PTm n) : PTm n := GaussianNamedPositiveLogarithm.data (inputData r x) margin

@[simp] theorem subst_inputData {l : ℕ} (σ : Fin n → PTm l) (r x : PTm n) :
    Syn.subst σ (inputData r x) = inputData (Syn.subst σ r) (Syn.subst σ x) := by simp [inputData,two,one]
@[simp] theorem subst_margin {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (margin : PTm n) = (margin : PTm l) := by simp [margin,two]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (r x : PTm n) :
    Syn.subst σ (data r x) = data (Syn.subst σ r) (Syn.subst σ x) := by simp [data]

theorem wallis_regular (r x : PTm n) : Γ ⊢[PRAAx] pointCN wallisF (wallisData r x) :=
  multiply_fast _ _ _ _ (GaussianGammaHalfPiName.name_regular x) (constant_regular _)

private theorem pi_real (x : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples P x := by
  refine .allI ?_
  let p : PTm (n+1) := var 0
  let X := Syn.shift x
  let Δ := Γ.map Fm.shift
  let A := num 4*BaselQuadrature.Q (GaussianGammaHalfPiName.meshAt p) (GaussianGammaHalfPiName.clearing p)
  let B := fact (GaussianGammaHalfPiName.clearing p)
  have hB : Δ ⊢[PRAAx] le one B := GaussianGammaHalfRisingFactorial.factorial_positive _
  have read : Δ ⊢[PRAAx] ap2 P p X ≐ fraction A B := GaussianGammaHalfPiName.sample_at p X
  exact .andI (GaussianRationalHorner.canonical_congr read (ofGaussian_canonical _ _ hB))
    (RationalGaussianEmbedding.axis_congr read.eqSymm (fraction_axis A B hB))

theorem wallis_real (r x : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples wallisF (wallisData r x) := by
  let N := succ r
  have h := even_square_positive (Γ := Γ) N
  exact multiply_real P C x (ratioFactor N) (pi_real x)
    (constant_real _ (ofGaussian_canonical _ _ h) (fraction_axis _ _ h))

private theorem from_rate (q N U : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) N)
    (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] upper (fstT qone) (fstT q) (num 3*U+N) (N*U)) :
    Γ ⊢[PRAAx] upper (fstT (marginPoint (two : PTm n))) (fstT q) one U := by
  let b := denominatorOf (fstT q)
  let v := numeratorOf (fstT q)
  let a := re (oneCode : PTm n)
  let L := RationalRepresentedUpper.left a b (N*U)
  let R := RationalRepresentedUpper.right v one b (num 3*U+N) (N*U)
  have old : Γ ⊢[PRAAx] zle L R :=
    RationalRepresentedUpper.to_signed _ _ a v one b (num 3*U+N) (N*U)
      (ofGaussian_represents _ _ (le_refl one)).andE₁ (RationalRepresentations.represents_self _) h
  apply RationalRepresentedUpper.from_signed _ _ a v two b one U (le_succ_self one)
    (RationalArgmin.denominator_positive (fstT q)) (ofGaussian_represents _ _ (le_succ_self one)).andE₁
    (RationalRepresentations.represents_self _)
  apply PolynomialBisection.zle_scale_cancel (c := N) hN
  apply zle_of_toZ (two*PolynomialBisection.slack L R+U*b*monus N (num 6))
  have e := zle_toZ old
  have j := natEq (eq_add_of_le hn)
  dsimp only [PolynomialBisection.slack,L,R,a]
  dsimp only [L,R,a] at e
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,
    GaussianRootAlgebra.re_one] at e ⊢
  ipra_simps
  linear_combination 2*e-𝔞 U*𝔞 b*j

theorem wallis_lower (p r x : PTm n) (h : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] upper (fstT (marginPoint (two : PTm n))) (fstT (ap2 wallisF p (wallisData r x))) one (unit p) := by
  let N := succ r
  let U := unit p
  have den := positive_product (Γ := Γ) N U (zero_lt_succ r) (unit_positive p)
  have e := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ den (wallis_rate p r x)
  exact from_rate _ N U h (zero_lt_succ r)
    (upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ den e))

theorem positive_wall (r x : PTm n) (h : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source wallisF (wallisData r x) two := by
  refine .andI (wallis_regular r x) (.andI (le_succ_self one) ?_)
  refine .allI (.allI ?_)
  let R := Syn.shift (Syn.shift r)
  let X := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hn : Δ ⊢[PRAAx] le (num 6) (succ R) := by simpa [Fm.shift,Syn.shift,R,Δ] using h.shift.shift
  have e := wallis_lower q R X hn
  have wide := upper_mono _ _ _ _ (unit p+unit q) (unit p*unit q) (unit_positive q) e
    (by ipra_le (Groth.ι (IPRA.Q.mk Δ (unit q)))^2)
  have align := upper_congr (congrFst (constant_at p (marginPoint two))).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) wide
  simpa [GaussianNamedRightHalfPlane.certificate,GaussianNamedPositiveExponentialOrder.realOrder,
      GaussianNamedRightHalfPlane.marginPoint,Syn.shift,ComplexLogarithmRemainder.oneCode,
      ComplexLogarithmRemainder.code,ZT.ofNat,Δ,R,X,p,q,one,two] using align

theorem log_source (r x : PTm n) (h : Γ ⊢[PRAAx] le (num 6) (succ r)) : Γ ⊢[PRAAx]
    GaussianNamedPositiveLogarithm.source retimed (inputData r x) margin (GaussianNameBounds.U wallisF (wallisData r x)) :=
  GaussianNamedPositiveLateLogSource.positive_source wallisF (wallisData r x) two (positive_wall r x h) (wallis_real r x)

theorem name_regular (r x : PTm n) (h : Γ ⊢[PRAAx] le (num 6) (succ r)) : Γ ⊢[PRAAx] pointCN nameF (data r x) :=
  GaussianNamedPositiveLogarithm.name_regular _ _ _ _ (log_source r x h)

theorem name_real (r x : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples nameF (data r x) :=
  positive_log_real _ _ _

def rawClock (p : PTm n) : PTm n := GaussianNamedPositiveLogarithm.clock p margin+threshold two

private theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (rawClock p) :=
  le_trans (le_succ_self p) (le_trans (le_add_right (succ p) _) (le_add_right _ _))

theorem ratio_log_rate (p r x : PTm n) (h : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data r x)) qzero
      (num 12*unit p+num 29*succ r) (succ r*unit p) := by
  let N := succ r
  let U := unit p
  let S := unit (succ p)
  let s := rawClock p
  let V := unit s
  let q := GaussianNamedPositiveLogarithm.clock p margin
  let y := inputData r x
  let a := GaussianNamedPositiveLogarithm.numerator retimed q y
  let b := GaussianNamedPositiveLogarithm.denominator retimed q y
  let B := N*U
  let A := num 3*U+N
  have hN := zero_lt_succ (Γ := Γ) r
  have ub : Γ ⊢[PRAAx] le one B := positive_product _ _ hN (unit_positive p)
  have hv := positive_product (Γ := Γ) N V hN (unit_positive s)
  have grow : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (clock_later p)
  have hlog := log_source r x h
  have domain := GaussianNamedPositiveLogarithm.decoded_domain retimed q y margin _ hlog
  have read : Γ ⊢[PRAAx] fraction a b ≐ ap2 wallisF s (wallisData r x) :=
    (GaussianNamedPositiveLogarithm.decoded_value retimed q y margin _ hlog).eqTrans
      (GaussianNamedPositiveLateLogSource.sample_at wallisF q (wallisData r x) two)
  have rad := distance_radius_mono _ _ (num 3*V+N) (N*V) A B hv ub
    (by dsimp only [A,B]; ipra_le 𝔞 N^2*sl grow) (wallis_rate s r x)
  have near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction one one) A B :=
    distance_congr read.eqSymm GaussianGammaFactorialValues.natural_one.eqSymm (.eqRefl _) (.eqRefl _) rad
  have cmp := GaussianCompactLogarithmBounds.original_gaussian_time_distance a b one one A B
    domain.andE₁.andE₂ (le_refl one) ub near
  have right : Γ ⊢[PRAAx] le one (margin*one) := by unfold margin; ipra_le 3
  have hd := positive_product (Γ := Γ) B S ub (unit_positive (succ p))
  have close := GaussianPositiveRationalLogarithmVariation.diagonal_native (succ p) a b one one margin A B
    domain.andE₁ (.andI (le_refl one) (le_refl one)) ub domain.andE₂.andE₁ right cmp
  have logOne := distance_radius_mono _ _ _ _ (num 8*B) (B*S) (unit_positive (succ p)) hd
    (by ipra_le 0) (GaussianCompactLogarithmBounds.sample_one_bound (succ p))
  have total := distance_triangle_same _ _ _ _ _ _ hd close logOne
  have late : Γ ⊢[PRAAx] le U S := GaussianExponentialReference.unit_monotone (le_succ_self p)
  have final : Γ ⊢[PRAAx] le (((margin*A)*S+num 17*B+num 8*B)*B)
      ((num 12*U+num 29*N)*(B*S)) := by
    dsimp only [A,B,margin]
    ipra_le 25*𝔞 N^2*𝔞 U*sl late
  exact distance_radius_mono _ _ _ _ _ _ hd ub final
    (distance_congr (GaussianNamedPositiveLogarithm.sample_at retimed p y margin).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) total)

theorem exponential_wall (r x : PTm n) (h : Γ ⊢[PRAAx] le (num 6) (succ r)) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF nameF) wallisF
      (GaussianGammaFiniteApproximantName.exponentialInputData nameF (data r x)) (wallisData r x) := by
  let z := data r x
  let R := GaussianNameBounds.U nameF z
  have hs := log_source r x h
  have ex := GaussianNamedPositiveLogarithm.exponential_input _ _ _ _ hs
  have out := GaussianNamedPositiveLogarithmExponential.original_recovery _ _ _ _ hs
  have changeClock := GaussianExponentialRadiusIndependence.same_input_cross nameF R _ z
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (name_regular r x h)) ex
  have retime := GaussianNamedPositiveLateLogSource.original_cross (Γ := Γ) wallisF (wallisData r x) two (wallis_regular r x)
  exact cross_trans _ _ _ _ _ _ changeClock (cross_trans _ _ _ _ _ _ out (cross_symm _ _ _ _ retime))

theorem actual_Stirling_Wallis_log_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (num 6) (succ (var 1)) ⟶ distanceBounded (ap2 nameF (var 2) (data (var 1) (var 0))) qzero
      (num 12*unit (var 2)+num 29*succ (var 1)) (succ (var 1)*unit (var 2))) :=
  closeUniv 3 (.impI (ratio_log_rate _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingWallisLogRate
