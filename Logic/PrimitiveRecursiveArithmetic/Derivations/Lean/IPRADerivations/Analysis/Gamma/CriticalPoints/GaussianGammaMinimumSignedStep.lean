import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerFirstDerivative
import IPRADerivations.Analysis.Gamma.GaussianGammaPositiveRationalProperness
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianOffDominantWeights
import IPRADerivations.Probability.MedianWeighted

/-!
# Small signed steps to the Gamma chord centers

For rational endpoints `a/b` and `c/b`, the weighted center with base
weight `W-1` is the endpoint of the signed step `(c-a)/(W*b)`.
A primitive recursive choice of `W` meets the original logarithmic Euler
derivative modulus in either direction. The resulting divided difference
uses the original Gamma names at the base and at the literal chord center.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumSignedStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open ComplexLogarithmRemainder (code scale normSq eval_re_code eval_im_code normSq_eval)
open GaussianEulerLogarithmicContinuity (modulus modulus_positive)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianGammaDigammaNative (derivativeData derivative_regular)
open GaussianGammaEulerFirstDerivative (original_first_derivative_rate base_source shifted_source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_iff)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg gammaData gamma_regular euler_real_source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "baseSource" => GaussianStirlingGammaLogarithm.source

def increment (a c : PTm n) : PTm n := code ⟨c,a⟩ (ZT.ofNat zero)
def centerNumerator (a c W : PTm n) : PTm n := pred W*a+c
def centerDenominator (b W : PTm n) : PTm n := W*b
def weight (p a b M : PTm n) : PTm n := two+M*modulus (p+num 6) one a b

def domain (a c b M : PTm n) : Fm PTm n :=
  baseSource a b ⋏ (le one c ⋏ (le a (M*b) ⋏ le c (M*b)))

def quotientData (a c b W : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data gammaF gammaF
    (gammaData (centerNumerator a c W) (centerDenominator b W))
    (gammaData a b) (increment a c) (centerDenominator b W)

@[simp] theorem subst_increment {k : ℕ} (σ : Fin n → PTm k) (a c : PTm n) :
    Syn.subst σ (increment a c) = increment (Syn.subst σ a) (Syn.subst σ c) := by
  simp [increment, code, ZT.ofNat]

@[simp] theorem subst_centerNumerator {k : ℕ} (σ : Fin n → PTm k) (a c W : PTm n) :
    Syn.subst σ (centerNumerator a c W) = centerNumerator (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ W) := by
  simp [centerNumerator]

@[simp] theorem subst_centerDenominator {k : ℕ} (σ : Fin n → PTm k) (b W : PTm n) :
    Syn.subst σ (centerDenominator b W) = centerDenominator (Syn.subst σ b) (Syn.subst σ W) := by
  simp [centerDenominator]

@[simp] theorem subst_weight {k : ℕ} (σ : Fin n → PTm k) (p a b M : PTm n) :
    Syn.subst σ (weight p a b M) = weight (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ M) := by
  simp [weight, one, two]

@[simp] theorem subst_domain {k : ℕ} (σ : Fin n → PTm k) (a c b M : PTm n) :
    (domain a c b M).subst σ = domain (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ M) := by
  simp [domain, one]

@[simp] theorem subst_quotientData {k : ℕ} (σ : Fin n → PTm k) (a c b W : PTm n) :
    Syn.subst σ (quotientData a c b W) = quotientData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ W) := by
  simp [quotientData]

theorem increment_norm (a c : PTm n) : Γ ⊢[PRAAx] normSq (increment a c) ≐ ad c a*ad c a := by
  have e := natEq (ad_sq (Γ := Γ) c a)
  apply deriveNat
  rw [normSq_eval]
  unfold increment
  rw [eval_re_code,eval_im_code,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination -e

private theorem norm_from_order (a c : PTm n) (d : PTm n)
    (hd : Γ ⊢[PRAAx] le one d) (he : Γ ⊢[PRAAx] le d (ad c a)) :
    Γ ⊢[PRAAx] le one (normSq (increment a c)) := by
  have h := le_trans hd he
  exact le_congr (by ipra_ring) (increment_norm a c).eqSymm (le_mul_mono h h)

theorem separated_norm (a c : PTm n) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] le one (normSq (increment a c)) := by
  refine .orE apart ?_ ?_
  · exact norm_from_order a c _ (GaussianEulerUnitLogarithmicMargin.gap_positive _ _ Prf.hyp0)
      (le_add_right _ _)
  · exact norm_from_order a c _ (GaussianEulerUnitLogarithmicMargin.gap_positive _ _ Prf.hyp0)
      (le_add_left _ _)

theorem increment_bounded (a c D A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le (B*ad c a) (A*D)) :
    Γ ⊢[PRAAx] bounded (ofGaussian (increment a c) D) A B := by
  apply (bounded_iff _ _ _ _ _ hD hB (ofGaussian_represents _ _ hD)).iffMpr
  have e := natEq (increment_norm (Γ := Γ) a c)
  exact le_congr (by apply deriveNat; ipra_simps; linear_combination -𝔞(B)^2*e)
    (by ipra_ring) (le_mul_mono h h)

theorem weight_lower (p a b M : PTm n) : Γ ⊢[PRAAx] le two (weight p a b M) :=
  le_add_right _ _

theorem denominator_positive (b W : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx] le one (centerDenominator b W) :=
  positive_product _ _ hw hb

theorem center_source (a c b W : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) (hw : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] baseSource (centerNumerator a c W) (centerDenominator b W) :=
  .andI (le_trans hc (le_add_left _ _)) (denominator_positive b W hb hw)

theorem absolute_gap_bound (a c b M : PTm n) (h : Γ ⊢[PRAAx] domain a c b M) :
    Γ ⊢[PRAAx] le (ad c a) (M*b) :=
  LeanProofs.IPRA.Probability.MedianWeighted.ad_le_of
    (le_trans h.andE₂.andE₂.andE₂ (le_add_left _ _))
    (le_trans h.andE₂.andE₂.andE₁ (le_add_left _ _))

theorem step_size (a c b M W : PTm n) (h : Γ ⊢[PRAAx] domain a c b M)
    (hw : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] bounded (ofGaussian (increment a c) (centerDenominator b W)) M W := by
  apply increment_bounded _ _ _ _ _ (denominator_positive _ _ h.andE₁.andE₂ hw) hw
  exact le_congr (mul_comm _ _) (by unfold centerDenominator; ipra_ring)
    (mul_le_mul_right W (absolute_gap_bound a c b M h))

theorem derivative_source (p a c b M : PTm n) (h : Γ ⊢[PRAAx] domain a c b M)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] GaussianGammaEulerFirstDerivative.source p (arg a) a b b (increment a c)
      (centerDenominator b (weight p a b M)) := by
  let N := modulus (p+num 6) one a b
  let W := weight p a b M
  have hp : Γ ⊢[PRAAx] le one W := le_trans (le_succ_self one) (weight_lower p a b M)
  have hd := denominator_positive _ _ h.andE₁.andE₂ hp
  have pay : Γ ⊢[PRAAx] le (N*ad c a) (one*centerDenominator b W) := by
    have cap := absolute_gap_bound a c b M h
    dsimp only [centerDenominator,W,weight]
    ipra_le 𝔞(N)*sl cap+2*𝔞(b)
  have near := increment_bounded a c (centerDenominator b W) one N hd (modulus_positive _ _ _ _) pay
  exact .andI (.andI (.andI (euler_real_source a b h.andE₁).andE₁ (.andI hd near))
    (separated_norm a c apart)) h.andE₁.andE₁

private theorem shifted_value (a c b W : PTm n) (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx]
    equal (shifted (arg a) b (increment a c) (centerDenominator b W))
      (scale b (arg (centerNumerator a c W))) := by
  have e := natEq (GaussianOffDominantWeights.positive_succ_pred W hw)
  apply equal_of_values
  · simp only [shifted,arg,increment,centerDenominator,centerNumerator,re_add,re_scale,re_one,eval_re_code]
    simp only [ZT.toZ]
    ipra_simps
    linear_combination (𝔞(a)*𝔞(b))*e
  · simp only [shifted,arg,increment,centerDenominator,centerNumerator,im_add,im_scale,im_one,
      eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring

theorem shifted_fraction (a c b W : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hw : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] ofGaussian (shifted (arg a) b (increment a c) (centerDenominator b W))
      (b*centerDenominator b W) ≐ fraction (centerNumerator a c W) (centerDenominator b W) := by
  have hD := denominator_positive _ _ hb hw
  exact (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (positive_product _ _ hb hD)
    (shifted_value a c b W hw)).eqTrans
    (GaussianGammaEncodingRescaling.fraction_rescale _ _ _ hD hb)

theorem original_chord_quotient_rate (p a c b M : PTm n) (h : Γ ⊢[PRAAx] domain a c b M)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] independentRate QF IF (quotientData a c b (weight p a b M))
      (derivativeData a b) one (GaussianCoefficientNameBounds.unit p) := by
  let W := weight p a b M
  let D := centerDenominator b W
  let N := centerNumerator a c W
  let z := shifted (arg a) b (increment a c) D
  let x := GaussianGammaReciprocalInverse.gammaData z (a+one) (b*D) (two*b)
  have hs := derivative_source p a c b M h apart
  have hm := shifted_source p (arg a) a b b (increment a c) D hs
  have hw : Γ ⊢[PRAAx] le one W := le_trans (le_succ_self one) (weight_lower p a b M)
  have hc := center_source a c b W h.andE₂.andE₁ h.andE₁.andE₂ hw
  have e := GaussianGammaPositiveRationalProperness.original_cross z (a+one) (b*D) (two*b) N D hm hc
    (shifted_fraction a c b W h.andE₁.andE₂ hw)
  have reg := GaussianEulerIntegralGammaIdentification.original_gamma_regular z (a+one) (b*D) (two*b) hm
  have base := gamma_regular a b h.andE₁
  have q := GaussianNamedDifferenceQuotientProperness.proper gammaF gammaF gammaF gammaF
    x (gammaData N D) (gammaData a b) (gammaData a b) (increment a c) D
    reg (gamma_regular _ _ hc) base base e (cross_refl _ _ base)
  exact GaussianNamedRateTransport.transport QF IF QF IF _ _ _ _ one (GaussianCoefficientNameBounds.unit p)
    (GaussianCoefficientNameBounds.unit_positive p)
    (original_first_derivative_rate p (arg a) a b b (increment a c) D hs)
    (cross_symm _ _ _ _ q) (cross_refl _ _ (derivative_regular a b h.andE₁))

theorem actual_original_Gamma_thin_chord_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((domain (var 1) (var 2) (var 3) (var 4) ⋏ (lt (var 1) (var 2) ⋎ lt (var 2) (var 1))) ⟶
      independentRate QF IF (quotientData (var 1) (var 2) (var 3) (weight (var 0) (var 1) (var 3) (var 4)))
        (derivativeData (var 1) (var 3)) one (GaussianCoefficientNameBounds.unit (var 0))) :=
  closeUniv 5 (.impI (original_chord_quotient_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumSignedStep
