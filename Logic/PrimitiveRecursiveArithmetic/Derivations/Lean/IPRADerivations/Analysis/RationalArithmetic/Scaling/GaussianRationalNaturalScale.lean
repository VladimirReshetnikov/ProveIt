import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianTranslatedNonconstant
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower

/-!
# Actual natural scaling of arbitrary Gaussian-rational codes

The numerical scalar multiplies the decoded numerator pair and retains
the computed positive raw denominator. All output components are normalized.
The unit law returns the canonical recoding of an arbitrary raw input;
literal input-code equality is asserted only with its canonical guard.
Addition and multiplication transport are derived from actual value
representations and native Gaussian coordinate identities.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalNaturalScale

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (ofGaussian represents canonical canonical_unique represents_congr qzero qadd qmul
    positive_product qadd_represents qmul_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (scale oneCode zeroCode mul add)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_values re_scale im_scale re_mul im_mul re_add im_add re_one im_one re_zero im_zero)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def natScale (t q : PTm n) : PTm n := ofGaussian (scale t (rawGaussian q)) (rawDen q)
def naturalPoint (t : PTm n) : PTm n := ofGaussian (scale t oneCode) one

ipra_subst natScale
ipra_subst naturalPoint

theorem natScale_canonical (t q : PTm n) : Γ ⊢[PRAAx] canonical (natScale t q) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (raw_den_positive q)

theorem natural_point_represents (t : PTm n) : Γ ⊢[PRAAx]
    represents (naturalPoint t) (scale t oneCode) one :=
  GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _)

theorem natScale_raw_represents (t q : PTm n) : Γ ⊢[PRAAx]
    represents (natScale t q) (scale t (rawGaussian q)) (rawDen q) :=
  GaussianRationalHorner.ofGaussian_represents _ _ (raw_den_positive q)

theorem natural_product_value (t a : PTm n) : Γ ⊢[PRAAx]
    equal (mul (scale t oneCode) a) (scale t a) := by
  apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ring

/-- The natural-point program at zero gives the canonical Gaussian zero. -/
theorem natural_point_zero : Γ ⊢[PRAAx] naturalPoint (zero : PTm n) ≐ qzero := by
  apply canonical_unique _ _ zeroCode one
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    _ (GaussianRationalHorner.zero_represents _)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents _)
  apply equal_of_values <;>
    simp only [re_scale,im_scale,re_one,im_one,re_zero,im_zero] <;> ipra_simps <;> ring

/-- The natural-point program at one gives the canonical Gaussian one. -/
theorem natural_point_one : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ ofGaussian oneCode one := by
  apply canonical_unique _ _ oneCode one
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    _ (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents _)
  apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring

theorem natural_point_add (a b : PTm n) : Γ ⊢[PRAAx]
    qadd (naturalPoint a) (naturalPoint b) ≐ naturalPoint (a+b) := by
  apply canonical_unique _ _ (scale (a+b) oneCode) one (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    _ (natural_point_represents _)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (qadd_represents _ _ _ _ _ (le_refl _) (natural_point_represents a) (natural_point_represents b))
  apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

theorem natural_point_mul (a b : PTm n) : Γ ⊢[PRAAx]
    qmul (naturalPoint a) (naturalPoint b) ≐ naturalPoint (a*b) := by
  have e : Γ ⊢[PRAAx] equal (mul (scale a oneCode) (scale b oneCode)) (scale (a*b) oneCode) := by
    refine GaussianRootAlgebra.equal_trans (natural_product_value a (scale b oneCode)) ?_
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ one (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    (represents_congr (.eqRefl _) e (one_mul one) (qmul_represents _ _ _ _ _ _ (le_refl one) (le_refl one)
      (natural_point_represents a) (natural_point_represents b))) (natural_point_represents _)

/-- The directly computed numerator scaling equals actual multiplication
by the computed Gaussian natural point, for arbitrary raw input codes. -/
theorem natScale_as_product (t q : PTm n) : Γ ⊢[PRAAx]
    natScale t q ≐ qmul (naturalPoint t) q := by
  have product := qmul_represents _ _ _ _ _ _ (le_refl one) (raw_den_positive q)
    (natural_point_represents (Γ := Γ) t) (raw_represents q)
  exact canonical_unique _ _ _ _ (natScale_canonical t q) (GaussianRationalHorner.qmul_canonical _ _)
    (raw_den_positive q) (natScale_raw_represents t q)
    (represents_congr (.eqRefl _) (natural_product_value t (rawGaussian q)) (one_mul _) product)

theorem natScale_represents (t q a E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] represents q a E) : Γ ⊢[PRAAx] represents (natScale t q) (scale t a) E :=
  represents_congr (natScale_as_product t q).eqSymm (natural_product_value t a) (one_mul _)
    (qmul_represents _ _ _ _ _ _ (le_refl one) hE (natural_point_represents t) hq)

theorem natScale_zero (q : PTm n) : Γ ⊢[PRAAx] natScale zero q ≐ qzero := by
  apply canonical_unique _ _ zeroCode (rawDen q) (natScale_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (raw_den_positive q)
    (hrv := GaussianRationalHorner.zero_represents _)
  exact represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_zero,im_zero] <;> ipra_simps <;> ring)
    (.eqRefl _) (natScale_raw_represents zero q)

theorem natScale_one (q : PTm n) : Γ ⊢[PRAAx] natScale one q ≐ recode q := by
  apply canonical_unique _ _ (rawGaussian q) (rawDen q) (natScale_canonical _ _) (recode_canonical q)
    (raw_den_positive q) (hrv := GaussianTranslatedNonconstant.recode_represents q)
  exact represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring)
    (.eqRefl _) (natScale_raw_represents one q)

theorem natScale_one_canonical (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    natScale one q ≐ q :=
  (natScale_one q).eqTrans (GaussianTranslatedNonconstant.recode_eq q hq)

theorem natScale_add (t u q : PTm n) : Γ ⊢[PRAAx]
    natScale (t+u) q ≐ qadd (natScale t q) (natScale u q) := by
  apply canonical_unique _ _ (add (scale t (rawGaussian q)) (scale u (rawGaussian q))) (rawDen q)
    (natScale_canonical _ _) (GaussianRationalHorner.qadd_canonical _ _) (raw_den_positive q)
    (hrv := qadd_represents _ _ _ _ _ (raw_den_positive q)
      (natScale_raw_represents t q) (natScale_raw_represents u q))
  exact represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_add,im_add] <;> ipra_simps <;> ring)
    (.eqRefl _) (natScale_raw_represents (t+u) q)

theorem natScale_product (t a b : PTm n) : Γ ⊢[PRAAx]
    qmul a (natScale t b) ≐ natScale t (qmul a b) := by
  have hp := positive_product (Γ := Γ) _ _ (raw_den_positive a) (raw_den_positive b)
  have original := qmul_represents _ _ _ _ _ _ (raw_den_positive a) (raw_den_positive b)
    (raw_represents (Γ := Γ) a) (raw_represents b)
  apply canonical_unique _ _ (scale t (mul (rawGaussian a) (rawGaussian b))) (rawDen a*rawDen b)
    (GaussianRationalHorner.qmul_canonical _ _) (natScale_canonical _ _) hp
    (hrv := natScale_represents _ _ _ _ hp original)
  exact represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale] <;> ring)
    (.eqRefl _) (qmul_represents _ _ _ _ _ _ (raw_den_positive a) (raw_den_positive b)
      (raw_represents a) (natScale_raw_represents t b))

/-- Natural scaling distributes over subtraction of Gaussian-rational codes. -/
theorem natScale_sub (t a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (natScale t a) (natScale t b) ≐
      natScale t (GaussianRationalMetric.qsub a b) :=
  (GaussianRationalSyntheticDivision.qsub_congr (natScale_as_product t a) (natScale_as_product t b)).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqTrans (natScale_as_product t _).eqSymm)

theorem natScale_multiply (t u q : PTm n) : Γ ⊢[PRAAx]
    natScale t (natScale u q) ≐ natScale (t*u) q := by
  apply canonical_unique _ _ (scale (t*u) (rawGaussian q)) (rawDen q)
    (natScale_canonical _ _) (natScale_canonical _ _) (raw_den_positive q)
    (hrv := natScale_raw_represents (t*u) q)
  exact represents_congr (.eqRefl _) (by
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring)
    (.eqRefl _) (natScale_represents _ _ _ _ (raw_den_positive q) (natScale_raw_represents u q))

theorem natScale_congr {t u q r : PTm n} (ht : Γ ⊢[PRAAx] t ≐ u) (hq : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] natScale t q ≐ natScale u r := by
  ipra_congr (natScale (var 0) (var 1) : PTm 2) with [ht, hq]

def scaleF : PR 2 := PTm.toPR (natScale (var 0) (var 1))
theorem program_at (t q : PTm n) : Γ ⊢[PRAAx] ap2 scaleF t q ≐ natScale t q := by
  simpa [scaleF,ap2] using toPR_eq (Γ := Γ) (natScale (var 0) (var 1) : PTm 2) ![t,q]

theorem natural_scale_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (natScale (var 0+var 1) (var 2) ≐ qadd (natScale (var 0) (var 2)) (natScale (var 1) (var 2))) :=
  closeUniv 3 (natScale_add _ _ _)
theorem natural_scale_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qmul (var 1) (natScale (var 0) (var 2)) ≐ natScale (var 0) (qmul (var 1) (var 2))) :=
  closeUniv 3 (natScale_product _ _ _)
theorem natural_scale_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (natScale one (var 0) ≐ recode (var 0)) := closeUniv 1 (natScale_one _)
theorem natural_scale_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 scaleF (var 0) (var 1) ≐ natScale (var 0) (var 1)) ⋏ canonical (ap2 scaleF (var 0) (var 1))) :=
  closeUniv 2 (.andI (program_at _ _) (GaussianRationalHorner.canonical_congr (program_at _ _) (natScale_canonical _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalNaturalScale
