import IPRADerivations.Analysis.GaussianRationalDirectionNormalizer
import IPRADerivations.Analysis.GaussianRationalPhaseCertificate
import IPRADerivations.Analysis.RationalNonnegativePowers
import IPRADerivations.Analysis.GaussianDominantScalarOrder

/-!
# The computed rational amplitude of a dominant pair

The phase is the actual product -b0*conjugate(bk). Its original decoded
denominators are retained in the computed numerator and denominator of
alpha=(A/B)^k*normSq(bk)/normalizer(phase,H). The two local radial-score
comparisons and the proved 65/64 normalizer bracket imply the amplitude
bounds. No desired amplitude, phase-value or denominator identity is an
input premise. All coefficients, radii, indices and precision are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantAlpha

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product represents)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalDirectionNormalizer (norm sixtyFour sixtyFive)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def phase (b0 bk : PTm n) : PTm n := GaussianRationalMetric.qnegative
  (GaussianRationalHorner.qmul b0 (GaussianRationalPhaseCertificate.conjugatePoint bk))
def radialScore (bk A B k : PTm n) : PTm n := RationalArithmetic.multiply
  (RationalNonnegativePowers.power A B (two*k)) (qnormSq bk)
def P (b0 bk A k H : PTm n) : PTm n := pw A k*norm bk*
  GaussianRationalDirectionNormalizer.factor (phase b0 bk) H*rawDen (phase b0 bk)
def Q (b0 bk B k H : PTm n) : PTm n := pw B k*(rawDen bk*rawDen bk)*
  GaussianRationalDirectionNormalizer.S (phase b0 bk) H
def alpha (b0 bk A B k H : PTm n) : PTm n := fraction (P b0 bk A k H) (Q b0 bk B k H)
def radialUpper (b0 bk A B k : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (radialScore bk A B k) (qnormSq b0)
def radialLower (b0 bk A B k D : PTm n) : Fm PTm n :=
  RationalArgmin.rationalLE (qnormSq b0)
    (RationalArithmetic.multiply (fraction (D*D) one) (radialScore bk A B k))

@[simp] theorem subst_phase {m : ℕ} (σ : Fin n → PTm m) (b0 bk : PTm n) :
    Syn.subst σ (phase b0 bk) = phase (Syn.subst σ b0) (Syn.subst σ bk) := by simp [phase]
@[simp] theorem subst_radialScore {m : ℕ} (σ : Fin n → PTm m) (bk A B k : PTm n) :
    Syn.subst σ (radialScore bk A B k) = radialScore (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [radialScore]
@[simp] theorem subst_P {m : ℕ} (σ : Fin n → PTm m) (b0 bk A k H : PTm n) :
    Syn.subst σ (P b0 bk A k H) = P (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ H) := by simp [P]
@[simp] theorem subst_Q {m : ℕ} (σ : Fin n → PTm m) (b0 bk B k H : PTm n) :
    Syn.subst σ (Q b0 bk B k H) = Q (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by simp [Q]
@[simp] theorem subst_alpha {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H : PTm n) :
    Syn.subst σ (alpha b0 bk A B k H) = alpha (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by simp [alpha]
@[simp] theorem subst_radialUpper {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k : PTm n) :
    (radialUpper b0 bk A B k).subst σ = radialUpper (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [radialUpper]
@[simp] theorem subst_radialLower {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k D : PTm n) :
    (radialLower b0 bk A B k D).subst σ = radialLower (Syn.subst σ b0) (Syn.subst σ bk) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ D) := by simp [radialLower]

theorem phase_represents (b0 bk : PTm n) : Γ ⊢[PRAAx]
    represents (phase b0 bk)
      (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.mul (rawGaussian b0)
        (GaussianRationalReciprocal.conjugate (rawGaussian bk)))) (rawDen b0*rawDen bk) :=
  GaussianRationalMetric.qnegative_represents _ _ _
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (raw_den_positive b0) (raw_den_positive bk)
      (raw_represents b0) (GaussianRationalPhaseCertificate.conjugate_represents _ _ _ (raw_represents bk)))

theorem phase_native_norm (b0 bk : PTm n) : Γ ⊢[PRAAx]
    normSq (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.mul (rawGaussian b0)
      (GaussianRationalReciprocal.conjugate (rawGaussian bk)))) ≐ norm b0*norm bk :=
  (ComplexLogarithmRemainder.normSq_neg _).eqTrans
    ((ComplexLogarithmRemainder.normSq_mul _ _).eqTrans
      (congrMul (.eqRefl _) (GaussianRationalReciprocal.norm_conjugate _)))

/-- The phase's actual reduced component denominators need not equal
the product of either original point's decoded denominators. -/
theorem phase_norm_clearing (b0 bk : PTm n) : Γ ⊢[PRAAx]
    norm (phase b0 bk)*(rawDen b0*rawDen b0)*(rawDen bk*rawDen bk) ≐
      norm b0*norm bk*(rawDen (phase b0 bk)*rawDen (phase b0 bk)) := by
  have hp := positive_product _ _ (raw_den_positive (Γ := Γ) b0) (raw_den_positive bk)
  have actual := GaussianRationalMetric.qnormSq_represents (Γ := Γ) (phase b0 bk) (rawGaussian (phase b0 bk))
    (rawDen (phase b0 bk)) (raw_den_positive _) (raw_represents _)
  have combined : Γ ⊢[PRAAx] RationalArithmetic.represents (qnormSq (phase b0 bk))
      (ZT.ofNat (norm b0*norm bk)) ((rawDen b0*rawDen bk)*(rawDen b0*rawDen bk)) :=
    GaussianRationalHorner.scalar_congr (.eqRefl _)
      (ZT.derive (by simpa only [ZT.toZ_ofNat] using natEq (phase_native_norm (Γ := Γ) b0 bk))) (.eqRefl _)
      (GaussianRationalMetric.qnormSq_represents _ _ _ hp (phase_represents b0 bk))
  have f := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ actual combined
    (RationalArgmin.reflexive (qnormSq (phase b0 bk)))
  have b := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ combined actual
    (RationalArgmin.reflexive (qnormSq (phase b0 bk)))
  exact le_antisymm (le_congr (by unfold norm; ipra_ring) (.eqRefl _) f)
    (le_congr (by ipra_ring) (by unfold norm; ipra_ring) b)

theorem phase_positive (b0 bk : PTm n) (h0 : Γ ⊢[PRAAx] le one (norm b0))
    (hk : Γ ⊢[PRAAx] le one (norm bk)) : Γ ⊢[PRAAx] le one (norm (phase b0 bk)) := by
  have product := positive_product (Γ := Γ) _ _ (positive_product _ _ h0 hk)
    (positive_product _ _ (raw_den_positive (phase b0 bk)) (raw_den_positive (phase b0 bk)))
  have scaled := le_congr (.eqRefl _) (phase_norm_clearing b0 bk).eqSymm product
  exact GaussianDominantScalarOrder.factor_positive_left (norm (phase b0 bk)) ((rawDen b0*rawDen b0)*(rawDen bk*rawDen bk))
    (le_congr (.eqRefl _) (by ipra_ring) scaled)

theorem power_double (A k : PTm n) : Γ ⊢[PRAAx] pw A (two*k) ≐ pw A k*pw A k :=
  (congrAp2 powF (by ipra_ring) (.eqRefl A)).eqTrans (pw_add A k k)

theorem radial_represents (bk A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (radialScore bk A B k) (ZT.ofNat (pw A k*pw A k*norm bk))
      ((pw B k*pw B k)*(rawDen bk*rawDen bk)) := by
  have result := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (RationalNonnegativePowers.power_represents A B (two*k) hB)
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive bk) (raw_represents bk))
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := congrMul (power_double B k) (.eqRefl _)) (h := result)
  apply ZT.derive
  have e := natEq (power_double (Γ := Γ) A k)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  unfold norm
  ipra_simps
  rw [e]

theorem radial_upper_cleared (b0 bk A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] radialUpper b0 bk A B k) : Γ ⊢[PRAAx]
    le (pw A k*pw A k*norm bk*(rawDen b0*rawDen b0))
      (pw B k*pw B k*norm b0*(rawDen bk*rawDen bk)) :=
  le_congr (by ipra_ring) (by unfold norm; ipra_ring)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ (radial_represents bk A B k hB)
      (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive b0) (raw_represents b0)) h)

theorem radial_lower_cleared (b0 bk A B k D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] radialLower b0 bk A B k D) : Γ ⊢[PRAAx]
    le (pw B k*pw B k*norm b0*(rawDen bk*rawDen bk))
      (D*D*pw A k*pw A k*norm bk*(rawDen b0*rawDen b0)) := by
  have scaledRaw := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents (D*D) one (le_refl one)) (radial_represents bk A B k hB)
  have scaled : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (fraction (D*D) one) (radialScore bk A B k))
      (ZT.ofNat (D*D*pw A k*pw A k*norm bk))
      ((pw B k*pw B k)*(rawDen bk*rawDen bk)) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := scaledRaw)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive b0) (raw_represents b0)) scaled h
  exact le_congr (by unfold norm; ipra_ring) (.eqRefl _) raw

/-- Pure natural cross-clearing: only the actual positive original
denominator is cancelled before the square comparison is removed. -/
theorem upper_kernel (r t u v a b c f s z : PTm n)
    (ha : Γ ⊢[PRAAx] le one a)
    (hPhase : Γ ⊢[PRAAx] z*a*a*b*b ≐ u*v*c*c)
    (hScore : Γ ⊢[PRAAx] le (r*r*v*a*a) (t*t*u*b*b))
    (hNormalizer : Γ ⊢[PRAAx] le (z*f*f) (s*s)) : Γ ⊢[PRAAx]
    le (r*v*f*c) (t*b*b*s) := by
  have first : Γ ⊢[PRAAx] le ((r*v*f*c)*(r*v*f*c)*(a*a))
      ((t*t*b*b*b*b*a*a)*(z*f*f)) := by
    apply le_congr (by ipra_ring) ?_ (mul_le_mul_right (v*f*f*c*c) hScore)
    apply deriveNat
    have e := natEq hPhase
    simp only [IPRA.Q.mk_mul,map_mul] at e
    ipra_simps
    linear_combination -(𝔞(t)*𝔞(t)*𝔞(b)*𝔞(b)*𝔞(f)*𝔞(f))*e
  have second : Γ ⊢[PRAAx] le ((t*t*b*b*b*b*a*a)*(z*f*f))
      ((t*b*b*s)*(t*b*b*s)*(a*a)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (t*t*b*b*b*b*a*a) hNormalizer)
  apply nat_sqrt_mono
  exact RationalValueBounds.positive_cancel (positive_product a a ha ha)
    (le_congr (by ipra_ring) (by ipra_ring) (le_trans first second))

theorem lower_kernel (r t u v a b c f s z D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a)
    (hPhase : Γ ⊢[PRAAx] z*a*a*b*b ≐ u*v*c*c)
    (hScore : Γ ⊢[PRAAx] le (t*t*u*b*b) (D*D*r*r*v*a*a))
    (hNormalizer : Γ ⊢[PRAAx] le (sixtyFour*sixtyFour*s*s) (sixtyFive*sixtyFive*z*f*f)) : Γ ⊢[PRAAx]
    le (sixtyFour*(t*b*b*s)) (sixtyFive*D*(r*v*f*c)) := by
  have first : Γ ⊢[PRAAx] le ((sixtyFour*(t*b*b*s))*(sixtyFour*(t*b*b*s))*(a*a))
      ((sixtyFive*sixtyFive*v*f*f*c*c)*(t*t*u*b*b)) := by
    apply le_congr (by ipra_ring) ?_ (mul_le_mul_right (t*t*b*b*b*b*a*a) hNormalizer)
    apply deriveNat
    have e := natEq hPhase
    simp only [IPRA.Q.mk_mul,map_mul] at e
    ipra_simps
    linear_combination (𝔞(sixtyFive)*𝔞(sixtyFive)*𝔞(t)*𝔞(t)*𝔞(b)*𝔞(b)*𝔞(f)*𝔞(f))*e
  have second : Γ ⊢[PRAAx] le ((sixtyFive*sixtyFive*v*f*f*c*c)*(t*t*u*b*b))
      ((sixtyFive*D*(r*v*f*c))*(sixtyFive*D*(r*v*f*c))*(a*a)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (sixtyFive*sixtyFive*v*f*f*c*c) hScore)
  apply nat_sqrt_mono
  exact RationalValueBounds.positive_cancel (positive_product a a ha ha)
    (le_congr (by ipra_ring) (by ipra_ring) (le_trans first second))

/-- This stronger relative estimate needs neither radial-score
comparison. It retains the two actual lengths separately. -/
theorem relative_kernel (r t u v a b c f s z : PTm n)
    (hPhase : Γ ⊢[PRAAx] z*a*a*b*b ≐ u*v*c*c)
    (hNormalizer : Γ ⊢[PRAAx] le (sixtyFour*sixtyFour*s*s) (sixtyFive*sixtyFive*z*f*f)) : Γ ⊢[PRAAx]
    le ((a*a)*((sixtyFour*(t*b*b*s))*(sixtyFour*(t*b*b*s))*(r*r*v)))
      (((sixtyFive*(r*v*f*c))*(sixtyFive*(r*v*f*c))*u)*(t*t*b*b)) := by
  apply le_congr (by ipra_ring) ?_ (mul_le_mul_right (t*t*b*b*b*b*a*a*r*r*v) hNormalizer)
  apply deriveNat
  have e := natEq hPhase
  simp only [IPRA.Q.mk_mul,map_mul] at e
  ipra_simps
  linear_combination (𝔞(sixtyFive)*𝔞(sixtyFive)*𝔞(t)*𝔞(t)*𝔞(b)*𝔞(b)*𝔞(f)*𝔞(f)*𝔞(r)*𝔞(r)*𝔞(v))*e

theorem denominator_positive (b0 bk B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (Q b0 bk B k H) := positive_product _ _
  (positive_product _ _ (RationalNonnegativePowers.denominator_positive B k hB)
    (positive_product _ _ (raw_den_positive bk) (raw_den_positive bk)))
  (GaussianRationalDirectionNormalizer.S_positive _ _)

theorem numerator_positive (b0 bk A k H : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hk : Γ ⊢[PRAAx] le one (norm bk)) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (P b0 bk A k H) := positive_product _ _
  (positive_product _ _ (positive_product _ _ (GaussianPolynomialPerturbation.power_positive A k hA) hk)
    (GaussianRationalDirectionNormalizer.factor_positive _ _ hH)) (raw_den_positive _)

theorem phase_product_clearing (b0 bk : PTm n) : Γ ⊢[PRAAx]
    norm (phase b0 bk)*rawDen b0*rawDen b0*rawDen bk*rawDen bk ≐
      norm b0*norm bk*rawDen (phase b0 bk)*rawDen (phase b0 bk) :=
  (by ipra_ring : Γ ⊢[PRAAx] _ ≐ norm (phase b0 bk)*(rawDen b0*rawDen b0)*(rawDen bk*rawDen bk)).eqTrans
    ((phase_norm_clearing b0 bk).eqTrans (by ipra_ring))

theorem alpha_le_one (b0 bk A B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUpper : Γ ⊢[PRAAx] radialUpper b0 bk A B k) : Γ ⊢[PRAAx]
    le (P b0 bk A k H) (Q b0 bk B k H) := by
  have actual := upper_kernel (pw A k) (pw B k) (norm b0) (norm bk) (rawDen b0) (rawDen bk)
    (rawDen (phase b0 bk)) (GaussianRationalDirectionNormalizer.factor (phase b0 bk) H)
    (GaussianRationalDirectionNormalizer.S (phase b0 bk) H) (norm (phase b0 bk)) (raw_den_positive b0)
    (phase_product_clearing b0 bk)
    (le_congr (by ipra_ring) (by ipra_ring) (radial_upper_cleared b0 bk A B k hB hUpper))
    (le_of_lt (GaussianRationalDirectionNormalizer.floor_upper _ _))
  exact le_congr (.eqRefl _) (by unfold Q; ipra_ring) actual

theorem alpha_lower_bound (b0 bk A B k H D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h0 : Γ ⊢[PRAAx] le one (norm b0)) (hk : Γ ⊢[PRAAx] le one (norm bk))
    (hH : Γ ⊢[PRAAx] le sixtyFour H)
    (hLower : Γ ⊢[PRAAx] radialLower b0 bk A B k D) : Γ ⊢[PRAAx]
    le (sixtyFour*Q b0 bk B k H) (sixtyFive*D*P b0 bk A k H) := by
  have actual := lower_kernel (pw A k) (pw B k) (norm b0) (norm bk) (rawDen b0) (rawDen bk)
    (rawDen (phase b0 bk)) (GaussianRationalDirectionNormalizer.factor (phase b0 bk) H)
    (GaussianRationalDirectionNormalizer.S (phase b0 bk) H) (norm (phase b0 bk)) D (raw_den_positive b0)
    (phase_product_clearing b0 bk)
    (le_congr (by ipra_ring) (by ipra_ring) (radial_lower_cleared b0 bk A B k D hB hLower))
    (le_congr (by ipra_ring) (.eqRefl _)
      (GaussianRationalDirectionNormalizer.normalizer_integer_upper _ _ (phase_positive b0 bk h0 hk) hH))
  exact le_congr (by unfold Q; ipra_ring) (.eqRefl _) actual

theorem alpha_represents (b0 bk A B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (alpha b0 bk A B k H) (ZT.ofNat (P b0 bk A k H)) (Q b0 bk B k H) :=
  fraction_represents _ _ (denominator_positive b0 bk B k H hB)

theorem natural_multiple_represents (W c u D : PTm n)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat u) D) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (RationalArithmetic.multiply (fraction W one) c) (ZT.ofNat (W*u)) D := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _)
    (h := RationalRepresentations.represents_multiply _ _ _ _ _ _ (fraction_represents W one (le_refl one)) hc)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

/-- The true relative bound follows directly from the actual normalizer
bracket. Neither radial comparison is an input to this stronger estimate. -/
theorem radial_relative_alpha (b0 bk A B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h0 : Γ ⊢[PRAAx] le one (norm b0)) (hk : Γ ⊢[PRAAx] le one (norm bk))
    (hH : Γ ⊢[PRAAx] le sixtyFour H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (fraction ((sixtyFour*Q b0 bk B k H)*(sixtyFour*Q b0 bk B k H)) one)
        (radialScore bk A B k))
      (RationalArithmetic.multiply (fraction ((sixtyFive*P b0 bk A k H)*(sixtyFive*P b0 bk A k H)) one)
        (qnormSq b0)) := by
  have bp := RationalNonnegativePowers.denominator_positive (Γ := Γ) B k hB
  have dp := raw_den_positive (Γ := Γ) bk
  have actual := relative_kernel (pw A k) (pw B k) (norm b0) (norm bk) (rawDen b0) (rawDen bk)
    (rawDen (phase b0 bk)) (GaussianRationalDirectionNormalizer.factor (phase b0 bk) H)
    (GaussianRationalDirectionNormalizer.S (phase b0 bk) H) (norm (phase b0 bk))
    (phase_product_clearing b0 bk)
    (le_congr (by ipra_ring) (.eqRefl _)
      (GaussianRationalDirectionNormalizer.normalizer_integer_upper _ _ (phase_positive b0 bk h0 hk) hH))
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ bp bp) (positive_product _ _ dp dp))
    (positive_product _ _ (raw_den_positive b0) (raw_den_positive b0))
    (natural_multiple_represents _ _ _ _ (radial_represents bk A B k hB))
    (natural_multiple_represents _ _ _ _
      (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive b0) (raw_represents b0)))
  exact le_congr (by unfold Q; ipra_ring) (by unfold P norm; ipra_ring) actual

/-- The actual fraction really is the source amplitude: multiplying it
by the computed normalizer gives the original coefficient norm times r^k. -/
theorem alpha_times_normalizer (b0 bk A B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (alpha b0 bk A B k H)
        (GaussianRationalDirectionNormalizer.normalizer (phase b0 bk) H) ≐
      RationalArithmetic.multiply (RationalNonnegativePowers.power A B k) (qnormSq bk) := by
  have lraw := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (alpha_represents b0 bk A B k H hB) (GaussianRationalDirectionNormalizer.normalizer_represents (phase b0 bk) H hH)
  have rraw := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (RationalNonnegativePowers.power_represents A B k hB)
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive bk) (raw_represents bk))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.multiply_guard _ _) (RationalArithmetic.multiply_guard _ _) lraw rraw
    (positive_product _ _ (denominator_positive b0 bk B k H hB)
      (GaussianRationalDirectionNormalizer.normalizer_denominator_positive _ _ hH))
    (positive_product _ _ (RationalNonnegativePowers.denominator_positive B k hB)
      (positive_product _ _ (raw_den_positive bk) (raw_den_positive bk)))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  unfold P Q norm
  ipra_simps
  ring

def certificate (b0 bk A B k H D : PTm n) : Fm PTm n :=
  le one (Q b0 bk B k H) ⋏ (le one (P b0 bk A k H) ⋏
    (le (P b0 bk A k H) (Q b0 bk B k H) ⋏
      le (sixtyFour*Q b0 bk B k H) (sixtyFive*D*P b0 bk A k H)))
@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H D : PTm n) :
    (certificate b0 bk A B k H D).subst σ = certificate (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) (Syn.subst σ D) := by simp [certificate]

theorem alpha_bounds (b0 bk A B k H D : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hH : Γ ⊢[PRAAx] le sixtyFour H) (_hD : Γ ⊢[PRAAx] le one D)
    (h0 : Γ ⊢[PRAAx] le one (norm b0)) (hk : Γ ⊢[PRAAx] le one (norm bk))
    (hUpper : Γ ⊢[PRAAx] radialUpper b0 bk A B k)
    (hLower : Γ ⊢[PRAAx] radialLower b0 bk A B k D) : Γ ⊢[PRAAx] certificate b0 bk A B k H D :=
  .andI (denominator_positive b0 bk B k H hB)
    (.andI (numerator_positive b0 bk A k H hA hk (GaussianRationalDirectionNormalizer.H_positive H hH))
      (.andI (alpha_le_one b0 bk A B k H hB hUpper) (alpha_lower_bound b0 bk A B k H D hB h0 hk hH hLower)))

def input (b0 bk A B k H D : PTm n) : Fm PTm n :=
  le one A ⋏ (le one B ⋏ (le sixtyFour H ⋏ (le one D ⋏
    (le one (norm b0) ⋏ (le one (norm bk) ⋏
      (radialUpper b0 bk A B k ⋏ radialLower b0 bk A B k D))))))
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H D : PTm n) :
    (input b0 bk A B k H D).subst σ = input (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) (Syn.subst σ D) := by simp [input]

theorem from_input (b0 bk A B k H D : PTm n) (h : Γ ⊢[PRAAx] input b0 bk A B k H D) : Γ ⊢[PRAAx]
    certificate b0 bk A B k H D := by
  have hB := Prf.andE₂ h
  have hH := Prf.andE₂ hB
  have hD := Prf.andE₂ hH
  have h0 := Prf.andE₂ hD
  have hk := Prf.andE₂ h0
  have hRadial := Prf.andE₂ hk
  exact alpha_bounds b0 bk A B k H D (Prf.andE₁ h) (Prf.andE₁ hB) (Prf.andE₁ hH)
    (Prf.andE₁ hD) (Prf.andE₁ h0) (Prf.andE₁ hk) (Prf.andE₁ hRadial) (Prf.andE₂ hRadial)

def output (b0 bk A B k H : PTm n) : PTm n := pairT (phase b0 bk)
  (pairT (P b0 bk A k H) (pairT (Q b0 bk B k H) (pairT (alpha b0 bk A B k H)
    (GaussianRationalDirectionNormalizer.normalizer (phase b0 bk) H))))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (b0 bk A B k H : PTm n) : PTm n := PTm.app outputF ![b0,bk,A,B,k,H]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H : PTm n) :
    Syn.subst σ (output b0 bk A B k H) = output (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (b0 bk A B k H : PTm n) :
    Syn.subst σ (run b0 bk A B k H) = run (Syn.subst σ b0) (Syn.subst σ bk)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (b0 bk A B k H : PTm n) : Γ ⊢[PRAAx] run b0 bk A B k H ≐ output b0 bk A B k H := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![b0,bk,A,B,k,H]

theorem returned_phase (b0 bk A B k H : PTm n) : Γ ⊢[PRAAx] fstT (run b0 bk A B k H) ≐ phase b0 bk :=
  (congrFst (program_at b0 bk A B k H)).eqTrans (fst_pair _ _)
theorem returned_numerator (b0 bk A B k H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run b0 bk A B k H)) ≐ P b0 bk A k H :=
  (congrFst ((congrSnd (program_at b0 bk A B k H)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (b0 bk A B k H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run b0 bk A B k H))) ≐ Q b0 bk B k H :=
  (congrFst ((congrSnd ((congrSnd (program_at b0 bk A B k H)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_alpha (b0 bk A B k H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run b0 bk A B k H)))) ≐ alpha b0 bk A B k H :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at b0 bk A B k H)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_normalizer (b0 bk A B k H : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run b0 bk A B k H)))) ≐
    GaussianRationalDirectionNormalizer.normalizer (phase b0 bk) H :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at b0 bk A B k H)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_phase_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (represents (phase (var 0) (var 1))
        (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.mul (rawGaussian (var 0))
          (GaussianRationalReciprocal.conjugate (rawGaussian (var 1))))) (rawDen (var 0)*rawDen (var 1)) ⋏
      norm (phase (var 0) (var 1))*(rawDen (var 0)*rawDen (var 0))*(rawDen (var 1)*rawDen (var 1)) ≐
        norm (var 0)*norm (var 1)*(rawDen (phase (var 0) (var 1))*rawDen (phase (var 0) (var 1)))) :=
  closeUniv 2 (.andI (phase_represents _ _) (phase_norm_clearing _ _))

theorem actual_alpha_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (from_input _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_relative_alpha_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (norm (var 0)) ⟶ le one (norm (var 1)) ⟶ le sixtyFour (var 5) ⟶
      RationalArgmin.rationalLE
        (RationalArithmetic.multiply
          (fraction ((sixtyFour*Q (var 0) (var 1) (var 3) (var 4) (var 5))*(sixtyFour*Q (var 0) (var 1) (var 3) (var 4) (var 5))) one)
          (radialScore (var 1) (var 2) (var 3) (var 4)))
        (RationalArithmetic.multiply
          (fraction ((sixtyFive*P (var 0) (var 1) (var 2) (var 4) (var 5))*(sixtyFive*P (var 0) (var 1) (var 2) (var 4) (var 5))) one)
          (qnormSq (var 0)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (radial_relative_alpha _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_alpha_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶
      RationalArithmetic.multiply (alpha (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (GaussianRationalDirectionNormalizer.normalizer (phase (var 0) (var 1)) (var 5)) ≐
        RationalArithmetic.multiply (RationalNonnegativePowers.power (var 2) (var 3) (var 4)) (qnormSq (var 1))) :=
  closeUniv 6 (.impI (.impI (alpha_times_normalizer _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_alpha_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
      ((fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ phase (var 0) (var 1)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐ P (var 0) (var 1) (var 2) (var 4) (var 5)) ⋏
          ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ Q (var 0) (var 1) (var 3) (var 4) (var 5)) ⋏
            ((fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))) ≐ alpha (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
              sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))) ≐
                GaussianRationalDirectionNormalizer.normalizer (phase (var 0) (var 1)) (var 5)))))) :=
  closeUniv 6 (.andI (program_at _ _ _ _ _ _) (.andI (returned_phase _ _ _ _ _ _)
    (.andI (returned_numerator _ _ _ _ _ _) (.andI (returned_denominator _ _ _ _ _ _)
      (.andI (returned_alpha _ _ _ _ _ _) (returned_normalizer _ _ _ _ _ _))))))

end LeanProofs.IPRA.Analysis.GaussianDominantAlpha
