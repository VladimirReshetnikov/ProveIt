import IPRADerivations.Analysis.Euler.Logarithms.LowerBounds.GaussianEulerLogarithmicLowerPointwise
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianLowerRootQuadratureBound
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactIntervalRescaling

/-!
# Actual logarithmic observations on the original lower-root partition

The numerical panel exponent is 2A-1, retaining the original margin 1/A.
The logarithmic compact modulus is computed on the fixed interval
[eta_q,1] and is unchanged under root-grid denominator rescaling.
Every actual right observation has the checked factorial reciprocal-root
majorant. No row norm or local modulus is an input hypothesis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerRootRows

open_ipra
open GaussianEulerLogarithmicLowerPointwise (degree exponent coefficient)
open GaussianEulerLogarithmicCompactName (evaluatorF)
open GaussianEulerLowerTailRootGrid (rootNumerator rootDenominator timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (totalWidth root_right_guard)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive height)
open GaussianGammaCompactCutoffGeometry (ratio lowerWidth lower_endpoint)
open GaussianCompactRiemannName (sampledModulus sampled_modulus_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def panelExponent (A : PTm n) : PTm n := exponent A
def panelDegree (A : PTm n) : PTm n := succ (panelExponent A)
def intervalDen (q A R : PTm n) : PTm n := etaDen q (panelDegree A) R
def lipschitz (j q A R : PTm n) : PTm n := GaussianEulerLogarithmicMultiplier.lipschitz j R (intervalDen q A R) one
def fixedData (j z R B q A : PTm n) : PTm n := GaussianEulerLogarithmicCompactName.fixedData j R (intervalDen q A R) one z B
def source (z R B H p q A : PTm n) : Fm PTm n := GaussianEulerLowerPowerCoefficients.source z R B A ⋏ (le one H ⋏ lt p q)

ipra_subst panelExponent
ipra_subst panelDegree
ipra_subst intervalDen [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst lipschitz
ipra_subst fixedData
ipra_subst source

theorem degree_identity (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] degree A ≐ panelDegree A :=
  RationalIntegerNormalization.positive_form (positive_product two A (le_succ_self one) hA)

theorem base_modulus (j z R B p q A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF one (lowerWidth p q (panelDegree A)) (intervalDen q A R) (lipschitz j q A R) (fixedData j z R B q A) := by
  let D := panelDegree A
  let E := intervalDen q A R
  have ratioBound : Γ ⊢[PRAAx] le (ratio p q D) E :=
    le_congr (one_mul _) ((mul_comm _ _).eqTrans (GaussianGammaCompactCutoffGeometry.eta_den_refinement p q D R hpq).eqSymm)
      (mul_le_mul_right (ratio p q D) (eta_den_positive p D R))
  have endpoint : Γ ⊢[PRAAx] le (one+lowerWidth p q D) (E*one) :=
    le_congr (lower_endpoint p q D).eqSymm (by ipra_ring) ratioBound
  exact GaussianEulerLogarithmicCompactName.sampled_modulus j z R B E one _
    (.andI (.andI h.andE₂.andE₁.andE₁ (.andI (eta_den_positive q D R) h.andE₂.andE₁.andE₂)) endpoint)

theorem root_modulus (j z R B H p q A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF (timeNumerator zero H p q (panelDegree A)) (totalWidth H p q (panelDegree A))
      (timeDenominator H q (panelDegree A) R) (lipschitz j q A R) (fixedData j z R B q A) := by
  let D := panelDegree A
  let K := pw H D
  have mod := GaussianCompactIntervalRescaling.rescaled_modulus evaluatorF K one (lowerWidth p q D)
    (intervalDen q A R) (lipschitz j q A R) (fixedData j z R B q A)
    (GaussianPolynomialPerturbation.power_positive H D hH) (base_modulus j z R B p q A h hpq)
  exact sampled_modulus_congr
    ((by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K).eqTrans (GaussianEulerLowerTailRootGrid.time_first H p q D).eqSymm)
    ((mul_comm _ _).eqTrans (GaussianEulerLowerTailRootGrid.time_width H p q D).eqSymm)
    ((mul_comm _ _).eqTrans (GaussianEulerLowerTailRootGrid.time_denominator H q D R).eqSymm)
    (.eqRefl _) (.eqRefl _) mod

private theorem domain_congr (a b c d E T : PTm n) (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d)
    (h : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain c d E T := by
  simpa only [GaussianCompactLogarithmBounds.subst_domain,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (GaussianCompactLogarithmBounds.domain (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
      ![a,b,E,T] ![c,d,E,T] (fun i => by fin_cases i; exact ha; exact hb; exact .eqRefl _; exact .eqRefl _) (by simpa using h)

theorem right_domain (i H p q A R : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] le p q)
    (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (pw (rootNumerator (succ i) H p q) (panelDegree A))
      (pw (rootDenominator H q (panelDegree A) R) (panelDegree A)) (intervalDen q A R) one := by
  let a := rootNumerator (succ i) H p q
  let b := rootDenominator H q (panelDegree A) R
  let D := panelDegree A
  let E := intervalDen q A R
  have guard := root_right_guard i H p q D R hH hpq hi
  have hb := positive_product (Γ := Γ) _ _ (unit_positive (height q D R)) hH
  have lowerRoot : Γ ⊢[PRAAx] le H a := le_add_right _ _
  have lowerRaw : Γ ⊢[PRAAx] le (E*pw H D) (E*pw a D) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E (pw_le_pw D lowerRoot))
  have lower : Γ ⊢[PRAAx] le (pw b D) (E*pw a D) :=
    le_congr (GaussianEulerLowerTailRootGrid.time_denominator H q D R).eqSymm (.eqRefl _) lowerRaw
  exact .andI (.andI (GaussianPolynomialPerturbation.power_positive a D guard.andE₁)
    (GaussianPolynomialPerturbation.power_positive b D hb))
    (.andI lower (le_congr (.eqRefl _) (one_mul (Γ := Γ) (pw b D)).eqSymm (pw_le_pw D guard.andE₂)))

theorem original_right_observation_bound (i s j z R B H p q A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (GaussianEulerLowerTailLocalComparison.rightTime i H p q (panelDegree A) R) (fixedData j z R B q A))
      (coefficient j A*pw (rootDenominator H q (panelDegree A) R) (panelExponent A)*unit s+
        pw (rootNumerator (succ i) H p q) (panelExponent A))
      (pw (rootNumerator (succ i) H p q) (panelExponent A)*unit s) := by
  let a := rootNumerator (succ i) H p q
  let b := rootDenominator H q (panelDegree A) R
  have guard := root_right_guard i H p q (panelDegree A) R hH hpq hi
  have hb := positive_product (Γ := Γ) _ _ (unit_positive (height q (panelDegree A) R)) hH
  have ea := congrAp2 powF (degree_identity A h.andE₁) (.eqRefl a)
  have eb := congrAp2 powF (degree_identity A h.andE₁) (.eqRefl b)
  have domain := domain_congr _ _ _ _ (intervalDen q A R) one ea.eqSymm eb.eqSymm (right_domain i H p q A R hH hpq hi)
  have src : Γ ⊢[PRAAx] GaussianEulerLogarithmicLowerPointwise.source z R B A (intervalDen q A R) one a b :=
    .andI (.andI h (.andI (.andI guard.andE₁ hb) guard.andE₂)) (.andI (eta_den_positive q (panelDegree A) R) domain)
  have original := GaussianEulerLogarithmicLowerPointwise.original_lower_pointwise s j z R B A (intervalDen q A R) one a b src
  have actual := (congrAp3 evaluatorF (.eqRefl s) (congrPairT ea eb).eqSymm (.eqRefl (fixedData j z R B q A))).eqTrans
    (GaussianEulerLogarithmicCompactName.sample_at s j R (intervalDen q A R) one z B _ _)
  exact bound_congr actual.eqSymm (.eqRefl _) (.eqRefl _) original

theorem original_logarithmic_lower_root_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      sampledModulus evaluatorF (timeNumerator zero (var 4) (var 5) (var 6) (panelDegree (var 7)))
        (totalWidth (var 4) (var 5) (var 6) (panelDegree (var 7))) (timeDenominator (var 4) (var 6) (panelDegree (var 7)) (var 2))
        (lipschitz (var 0) (var 6) (var 7) (var 2)) (fixedData (var 0) (var 1) (var 2) (var 3) (var 6) (var 7))) :=
  closeUniv 8 (.impI (root_modulus _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ (le_of_lt Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerRootRows
