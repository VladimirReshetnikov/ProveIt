import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerDerivativeQuotient
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneSigned
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality

/-!
# Common-denominator Taylor inputs for signed Gaussian samples

Two certified rational samples retain their values, positive real margins
and disk bounds when written over the product of their denominators. The
original distance bounds the computed Euler displacement radius, giving
uniform Taylor and difference-quotient guards in the sample metric.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerCommonDenominator

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (eval_im_code eval_re_code normSq scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (recode recode_canonical recode_represents)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator realNumerator sign)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product represents represents_congr)
open GaussianRationalL1 (rawGaussian raw_den_positive)
open GaussianRationalMetric (bounded_difference_iff distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRationalValueEquality (commonDen common_den_positive common_left_represents common_right_represents)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRootAlgebra
  (equal equal_of_values equal_re equal_im equal_symm equal_trans im_scale normSq_equal re_scale)
open RationalArithmetic (select select_zero select_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "ResidualSource" => GaussianLogGammaEulerResidualDomain.source
local notation "stepRadius" => GaussianLogGammaEulerStepReciprocal.radius
local notation "Step" => GaussianLogGammaEulerStepReciprocal.numerator
local notation "uniformSource" => GaussianLogGammaEulerDerivativeQuotient.uniformSource
local notation "quotientF" => GaussianLogGammaEulerDerivativeQuotient.nameF
local notation "slopeF" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF

def commonReal (q r : PTm n) : PTm n := denominator r * realNumerator q
def commonImag (q r : PTm n) : PTm n := denominator r * imagNumerator q
def commonNative (q r : PTm n) : PTm n := native (commonReal q r) (commonImag q r) (sign q)
def displacement (q r : PTm n) : PTm n :=
  Step (commonReal q r) (commonImag q r) (sign q) (commonReal r q) (commonImag r q) (sign r)

def sizeBound (R S : PTm n) : PTm n := two*(R+S)

ipra_subst commonReal

ipra_subst commonImag

ipra_subst commonNative

ipra_subst displacement

ipra_subst sizeBound

private theorem signed_scale (k B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] ZT.eq (signedImag (k*B) neg) (ZT.ofNat k * signedImag B neg) := by
  refine .orE h ?_ ?_
  · let Δ := (neg ≐ zero) :: Γ
    have a := natEq (select_zero (Γ := Δ) neg (k*B) zero Prf.hyp0)
    have b := natEq (select_zero (Γ := Δ) neg zero (k*B) Prf.hyp0)
    have c := natEq (select_zero (Γ := Δ) neg B zero Prf.hyp0)
    have d := natEq (select_zero (Γ := Δ) neg zero B Prf.hyp0)
    apply ZT.derive
    rw [ZT.toZ_mul, ZT.toZ_ofNat]
    simp only [signedImag, ZT.toZ]
    rw [a,b,c,d]
    ipra_simps
    ring
  · let Δ := (neg ≐ one) :: Γ
    have a := natEq (select_one (Γ := Δ) neg (k*B) zero Prf.hyp0)
    have b := natEq (select_one (Γ := Δ) neg zero (k*B) Prf.hyp0)
    have c := natEq (select_one (Γ := Δ) neg B zero Prf.hyp0)
    have d := natEq (select_one (Γ := Δ) neg zero B Prf.hyp0)
    apply ZT.derive
    rw [ZT.toZ_mul, ZT.toZ_ofNat]
    simp only [signedImag, ZT.toZ]
    rw [a,b,c,d]
    ipra_simps
    ring

theorem native_scaled (k A B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] equal (native (k*A) (k*B) neg) (scale k (native A B neg)) := by
  have hi := ZT.toZ_eq (signed_scale k B neg h)
  apply equal_of_values
  · simp only [re_scale, native, eval_re_code, ZT.toZ_ofNat]
    ipra_simps
  · simpa only [im_scale, native, eval_im_code, ZT.toZ_mul, ZT.toZ_ofNat] using hi

private theorem rescaled_source (q R K k D : PTm n) (h : Γ ⊢[PRAAx] certificate q R K)
    (hk : Γ ⊢[PRAAx] le one k) (hD : Γ ⊢[PRAAx] denominator q*k ≐ D) : Γ ⊢[PRAAx]
    ResidualSource (k*realNumerator q) (k*imagNumerator q) D (sign q) R ⋏
      le D (K*(k*realNumerator q)) := by
  have src := h.andE₁.andE₁
  have eNative := native_scaled k (realNumerator q) (imagNumerator q) (sign q) src.andE₁.andE₂
  have radii : Γ ⊢[PRAAx] k*(R*denominator q) ≐ R*D :=
    (show Γ ⊢[PRAAx] k*(R*denominator q) ≐ R*(denominator q*k) from by ipra_ring).eqTrans
      (congrMul (.eqRefl R) hD)
  have hd := le_congr (.eqRefl _) hD (positive_product _ _ src.andE₂ hk)
  have disk := le_congr (normSq_equal eNative).eqSymm (congrMul radii radii)
    (ComplexLogarithmRemainder.bounded_scale k h.andE₁.andE₂)
  have margin : Γ ⊢[PRAAx] le D (K*(k*realNumerator q)) :=
    le_congr hD (by ipra_ring) (mul_le_mul_right k h.andE₂.andE₁)
  exact .andI (.andI (.andI (.andI (positive_product _ _ hk src.andE₁.andE₁) src.andE₁.andE₂) hd) disk)
    margin

theorem common_sources (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K) : Γ ⊢[PRAAx]
    ResidualSource (commonReal q r) (commonImag q r) (commonDen q r) (sign q) R ⋏
      (ResidualSource (commonReal r q) (commonImag r q) (commonDen q r) (sign r) S ⋏
        (le (commonDen q r) (K*commonReal q r) ⋏ le (commonDen q r) (K*commonReal r q))) := by
  have l := rescaled_source q R K (denominator r) (commonDen q r) hq (raw_den_positive r) (.eqRefl _)
  have r' := rescaled_source r S K (denominator q) (commonDen q r) hr (raw_den_positive q) (mul_comm _ _)
  exact .andI l.andE₁ (.andI r'.andE₁ (.andI l.andE₂ r'.andE₂))

private theorem common_native_value (q r R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] equal (commonNative q r) (scale (denominator r) (rawGaussian q)) := by
  have hs := h.andE₁.andE₁.andE₁
  have v := GaussianNamedRightHalfPlaneSigned.native_value q hs.andE₁
  refine equal_trans (native_scaled (denominator r) _ _ (sign q) hs.andE₂) ?_
  apply equal_of_values
  · rw [re_scale, re_scale, equal_re v]
  · rw [im_scale, im_scale, equal_im v]

theorem left_represents (q r R K : PTm n) (h : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] represents q (commonNative q r) (commonDen q r) :=
  represents_congr (.eqRefl _) (equal_symm (common_native_value q r R K h)) (.eqRefl _)
    (common_left_represents q r)

theorem right_represents (q r S K : PTm n) (h : Γ ⊢[PRAAx] certificate r S K) :
    Γ ⊢[PRAAx] represents r (commonNative r q) (commonDen q r) :=
  represents_congr (.eqRefl _) (equal_symm (common_native_value r q S K h)) (.eqRefl _)
    (common_right_represents q r)

private theorem point_eq_recode (q w D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] represents q w D) : Γ ⊢[PRAAx] ofGaussian w D ≐ recode q := by
  let d := denominator q
  let E := D*d
  have l := rescale_to (ofGaussian w D) w D d E (ofGaussian_represents w D hD) (.eqRefl _)
  have r := rescale_to (Γ := Γ) (recode q) (rawGaussian q) d D E (recode_represents q) (mul_comm _ _)
  have cross := GaussianDominantPairAlgebra.represents_cross q w (rawGaussian q) D d h
    (GaussianRationalL1.raw_represents q)
  exact canonical_unique _ _ _ E (ofGaussian_canonical w D hD) (recode_canonical q)
    (positive_product D d hD (raw_den_positive q)) l
    (represents_congr (.eqRefl _) (equal_symm cross) (.eqRefl _) r)

theorem common_arguments (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K) : Γ ⊢[PRAAx]
    (argument (commonReal q r) (commonImag q r) (commonDen q r) (sign q) ≐ recode q) ⋏
      (argument (commonReal r q) (commonImag r q) (commonDen q r) (sign r) ≐ recode r) :=
  .andI (point_eq_recode _ _ _ (common_den_positive q r) (left_represents q r R K hq))
    (point_eq_recode _ _ _ (common_den_positive q r) (right_represents q r S K hr))

theorem cleared_distance (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hQ : Γ ⊢[PRAAx] le one Qd) : Γ ⊢[PRAAx]
    Fm.iff (distanceBounded r q P Qd)
      (le ((Qd*Qd)*normSq (displacement q r)) ((P*P)*(commonDen q r*commonDen q r))) :=
  bounded_difference_iff r q _ _ _ P Qd (common_den_positive q r) hQ
    (right_represents q r S K hr) (left_represents q r R K hq)

theorem punctured (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hne : Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot)) :
    Γ ⊢[PRAAx] le one (normSq (displacement q r)) := by
  refine .orE (zero_or_succ (normSq (displacement q r))) ?_ ?_
  · have e : ((normSq (displacement q r) ≐ zero) :: Γ) ⊢[PRAAx]
        (one*one)*normSq (displacement q r) ≐ zero :=
        (congrMul (.eqRefl (one*one)) Prf.hyp0).eqTrans (mul_zero _)
    have zeroDistance := (cleared_distance q r R S K zero one hq.wk hr.wk (le_refl one)).iffMpr
      (le_congr e.eqSymm (by ipra_ring) (le_refl zero))
    exact .botE _ (.impE hne.wk zeroDistance)
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

theorem radius_from_distance (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hQ : Γ ⊢[PRAAx] le one Qd) (h : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hn : Γ ⊢[PRAAx] le one (normSq (displacement q r))) : Γ ⊢[PRAAx]
    le (stepRadius (displacement q r)*Qd) (two*P*commonDen q r) := by
  let δ := displacement q r
  let E := GaussianLogGammaEulerStepReciprocal.lower δ
  let D := commonDen q r
  have hsq := le_trans (le_mul_mono (le_refl (Qd*Qd)) (isqrt_le (normSq δ)))
    ((cleared_distance q r R S K P Qd hq hr hQ).iffMp h)
  have low : Γ ⊢[PRAAx] le (E*Qd) (P*D) := by
    apply nat_sqrt_mono
    exact le_congr (by unfold E GaussianLogGammaEulerStepReciprocal.lower; ipra_ring) (by ipra_ring) hsq
  have cap := mul_le_mul_right Qd (GaussianLogGammaEulerStepReciprocal.radius_le_twice_lower δ hn)
  exact le_trans cap (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl two) low))

/-- A displacement radius suitable for continuity, including coincident inputs. -/
def continuityRadius (δ : PTm n) : PTm n :=
  select (eqb (normSq δ) zero) (stepRadius δ) zero

ipra_subst continuityRadius

theorem continuity_radius_from_distance (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hQ : Γ ⊢[PRAAx] le one Qd) (h : Γ ⊢[PRAAx] distanceBounded r q P Qd) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (displacement q r) (continuityRadius (displacement q r)) ⋏
      le (continuityRadius (displacement q r)*Qd) (two*P*commonDen q r) := by
  let δ := displacement q r
  refine .orE (zero_or_succ (normSq δ)) ?_ ?_
  · let Δ := (normSq δ ≐ zero) :: Γ
    have hz : Δ ⊢[PRAAx] normSq δ ≐ zero := Prf.hyp0
    have e : Δ ⊢[PRAAx] continuityRadius δ ≐ zero :=
      select_one _ _ _ (eqb_of_eq hz)
    have sq := (congrMul e e).eqTrans (zero_mul _)
    have mul := (congrMul e (.eqRefl Qd)).eqTrans (zero_mul _)
    exact .andI (le_congr hz.eqSymm sq.eqSymm (le_refl zero)) (le_congr mul.eqSymm (.eqRefl _) (zero_le _))
  · let Δ := (normSq δ ≐ succ (pred (normSq δ))) :: Γ
    have hs : Δ ⊢[PRAAx] normSq δ ≐ succ (pred (normSq δ)) := Prf.hyp0
    have hn : Δ ⊢[PRAAx] le one (normSq δ) := Order.zero_lt_of_eq_succ hs
    have e : Δ ⊢[PRAAx] continuityRadius δ ≐ stepRadius δ :=
      select_zero _ _ _ (eqb_zero_of_gt hn)
    exact .andI (le_congr (.eqRefl _) (congrMul e.eqSymm e.eqSymm)
      (GaussianLogGammaEulerStepReciprocal.native_bounded δ))
      (le_congr (congrMul e.eqSymm (.eqRefl _)) (.eqRefl _)
        (radius_from_distance q r R S K P Qd hq.wk hr.wk hQ.wk h.wk hn))

private theorem numerators_of_disk (A B D s R : PTm n)
    (h : Γ ⊢[PRAAx] ResidualSource A B D s R) : Γ ⊢[PRAAx] le A (R*D) ⋏ le B (R*D) := by
  have hs := le_congr (GaussianLogGammaEulerResidualRadius.native_norm A B s h.andE₁.andE₁.andE₂)
    (.eqRefl _) h.andE₂
  exact .andI (nat_sqrt_mono (le_trans (le_add_right (A*A) (B*B)) hs))
    (nat_sqrt_mono (le_trans (le_add_left (B*B) (A*A)) hs))

theorem common_size (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K) : Γ ⊢[PRAAx]
    le (commonReal q r+commonImag q r+commonReal r q+commonImag r q) (sizeBound R S*commonDen q r) := by
  have sources := common_sources q r R S K hq hr
  have l := numerators_of_disk _ _ _ _ _ sources.andE₁
  have r' := numerators_of_disk _ _ _ _ _ sources.andE₂.andE₁
  unfold sizeBound
  ipra_le sl l.andE₁ + sl l.andE₂ + sl r'.andE₁ + sl r'.andE₂

private theorem pay_radius (H D P Qd W : PTm n) (hQ : Γ ⊢[PRAAx] le one Qd)
    (hRadius : Γ ⊢[PRAAx] le (H*Qd) (two*P*D))
    (hPay : Γ ⊢[PRAAx] le (two*P*W) Qd) : Γ ⊢[PRAAx] le (H*W) D := by
  apply RationalValueBounds.positive_cancel hQ
  ipra_le 𝔞(W)*sl hRadius + 𝔞(D)*sl hPay

def admissionBudget (P K C : PTm n) : PTm n := num 256*P*(C+one)*(K*K)

theorem uniform_source (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) (hQ : Γ ⊢[PRAAx] le one Qd)
    (h : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hn : Γ ⊢[PRAAx] le one (normSq (displacement q r)))
    (hp : Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd) : Γ ⊢[PRAAx]
    uniformSource (commonReal q r) (commonImag q r) (sign q) (commonReal r q) (commonImag r q) (sign r)
      (commonDen q r) K (sizeBound R S) := by
  let D := commonDen q r
  let H := stepRadius (displacement q r)
  let C := sizeBound R S
  let W := num 128*(C+one)*(K*K)
  have hRadius := radius_from_distance q r R S K P Qd hq hr hQ h hn
  have hPay : Γ ⊢[PRAAx] le (two*P*W) Qd :=
    le_congr (by unfold admissionBudget W C; ipra_ring) (.eqRefl _) hp
  have small : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmIncrementMargin.smallStep H K C D :=
    le_congr (by unfold W; ipra_ring)
      (.eqRefl _) (pay_radius H D P Qd W hQ hRadius hPay)
  have sources := common_sources q r R S K hq hr
  exact .andI (.andI sources.andE₁.andE₁ (.andI sources.andE₂.andE₁.andE₁
    (.andI (GaussianLogGammaEulerStepReciprocal.native_bounded (displacement q r))
      (.andI hK (.andI sources.andE₂.andE₂.andE₁ (.andI sources.andE₂.andE₂.andE₂
        (.andI (common_size q r R S K hq hr) small))))))) hn

def quotientData (q r : PTm n) : PTm n :=
  GaussianLogGammaEulerDerivativeQuotient.data (commonReal q r) (commonImag q r) (sign q)
    (commonReal r q) (commonImag r q) (sign r) (commonDen q r)

def slopeData (q r : PTm n) : PTm n :=
  GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
    (commonReal q r) (commonImag q r) (commonDen q r) (sign q)

def rateBudget (P K : PTm n) : PTm n := num 16 * P * (K*K+two)

theorem quotient_rate (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) (hQ : Γ ⊢[PRAAx] le one Qd)
    (h : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hne : Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot))
    (hp : Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd) : Γ ⊢[PRAAx]
    independentRate quotientF slopeF (quotientData q r) (slopeData q r) (rateBudget P K) Qd := by
  let D := commonDen q r
  let E := GaussianLogGammaEulerDerivativeQuotient.errorNumerator (stepRadius (displacement q r)) K
  have hn := punctured q r R S K hq hr hne
  have u := uniform_source q r R S K P Qd hq hr hK hQ h hn hp
  have bound := mul_le_mul_right (num 8*(K*K+two)) (radius_from_distance q r R S K P Qd hq hr hQ h hn)
  have radius : Γ ⊢[PRAAx] le (E*Qd) (rateBudget P K*D) :=
    le_congr (by unfold E GaussianLogGammaEulerDerivativeQuotient.errorNumerator; ipra_ring)
      (by unfold rateBudget D; ipra_ring) bound
  exact GaussianNamedRateRadius.weaken quotientF slopeF (quotientData q r) (slopeData q r)
    E D (rateBudget P K) Qd (common_den_positive q r) hQ radius
    (GaussianLogGammaEulerDerivativeQuotient.uniform_rate _ _ _ _ _ _ _ _ _ u)

theorem quotient_modulus (q r R S K P Qd t : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) (hQ : Γ ⊢[PRAAx] le one Qd)
    (h : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hne : Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot))
    (hp : Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd)
    (ht : Γ ⊢[PRAAx] le (rateBudget P K*unit t) Qd) : Γ ⊢[PRAAx]
    independentRate quotientF slopeF (quotientData q r) (slopeData q r) one (unit t) :=
  GaussianNamedRateRadius.weaken quotientF slopeF (quotientData q r) (slopeData q r) _ Qd one (unit t)
    hQ (unit_positive t) (le_congr (.eqRefl _) (one_mul Qd).eqSymm ht)
    (quotient_rate q r R S K P Qd hq hr hK hQ h hne hp)

theorem actual_retimed_quotient_modulus (f g : PR 2) (x y M i j P Qd t : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x M)
    (hg : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source g y M) :
    let q := GaussianNamedRightHalfPlaneSigned.sample f x M i
    let r := GaussianNamedRightHalfPlaneSigned.sample g y M j
    let K := two*M
    let R := GaussianNamedRightHalfPlane.radius f x
    let S := GaussianNamedRightHalfPlane.radius g y
    (Γ ⊢[PRAAx] le one Qd) →
    (Γ ⊢[PRAAx] distanceBounded r q P Qd) →
    (Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot)) →
    (Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd) →
    (Γ ⊢[PRAAx] le (rateBudget P K*unit t) Qd) →
    (Γ ⊢[PRAAx] independentRate quotientF slopeF (quotientData q r) (slopeData q r) one (unit t)) := by
  dsimp only
  intro hQ h hne hp ht
  have htM : Γ ⊢[PRAAx] le one (two*M) := positive_product _ _ (zero_lt_succ _) hf.andE₂.andE₁
  exact quotient_modulus _ _ _ _ _ P Qd t
    (GaussianNamedRightHalfPlaneSigned.actual_retimed f x M i hf)
    (GaussianNamedRightHalfPlaneSigned.actual_retimed g y M j hg)
    htM hQ h hne hp ht

theorem actual_named_log_Gamma_sample_quotient_modulus_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let x := var 0
       let y := var 1
       let M := var 2
       let q := GaussianNamedRightHalfPlaneSigned.sample f x M (var 3)
       let r := GaussianNamedRightHalfPlaneSigned.sample g y M (var 4)
       let P := var 5
       let Qd := var 6
       let t := var 7
       let K := two*M
       let R := GaussianNamedRightHalfPlane.radius f x
       let S := GaussianNamedRightHalfPlane.radius g y
       (GaussianNamedRightHalfPlane.source f x M ⋏ GaussianNamedRightHalfPlane.source g y M) ⟶
       (le one Qd ⋏ (distanceBounded r q P Qd ⋏ ((distanceBounded r q zero one ⟶ .bot) ⋏
         (le (admissionBudget P K (sizeBound R S)) Qd ⋏ le (rateBudget P K*unit t) Qd)))) ⟶
       independentRate quotientF slopeF (quotientData q r) (slopeData q r) one (unit t)) := by
  refine closeUniv 8 (.impI (.impI ?_))
  exact actual_retimed_quotient_modulus f g _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerCommonDenominator
