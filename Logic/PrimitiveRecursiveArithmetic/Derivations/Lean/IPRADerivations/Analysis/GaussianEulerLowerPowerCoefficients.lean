import IPRADerivations.Analysis.GaussianEulerUpperPowerCoefficients

/-!
# Actual signed lower-time Euler power coefficients

The original native lower real-part certificate is A*Re(z)>=B.
It implies the original coefficient (z/B-1) is at least (1/A-1)
in scalar value. Actual conjugate sums double this order. The ordered
harmonic logarithm has genuinely nonpositive actual observations for
times below one, so original scalar multiplication reverses the order.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re oneCode)
open GaussianEulerIntegrandName (coefficient)
open GaussianEulerUpperPowerCoefficients (realMultiplier)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticBounds (natCode)
open RationalSupMetric (numeratorOf denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def realLower (z A B : PTm n) : Fm PTm n := zle (ZT.ofNat B) (ZT.ofNat A*re z)
def source (z R B A : PTm n) : Fm PTm n := le one A ⋏
  (GaussianEulerUpperPowerCoefficients.source z R B ⋏ realLower z A B)
def lowerMultiplier (A : PTm n) : PTm n := realMultiplier oneCode A
def amplification (R : PTm n) : PTm n := two*(R+two)
@[simp] theorem subst_native_order {m : ℕ} (σ : Fin n → PTm m) (u v : ZT n) :
    (zle u v).subst σ = zle (u.subst σ) (v.subst σ) := by simp [zle,ZT.subst]
@[simp] theorem subst_realLower {m : ℕ} (σ : Fin n → PTm m) (z A B : PTm n) :
    (realLower z A B).subst σ = realLower (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [realLower,subst_native_order,ZT.subst_mul,ZT.subst_ofNat,ComplexLogarithmRemainder.subst_re]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    (source z R B A).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by simp [source]
@[simp] theorem subst_lowerMultiplier {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (lowerMultiplier A) = lowerMultiplier (Syn.subst σ A) := by simp [lowerMultiplier]
@[simp] theorem subst_amplification {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (amplification R) = amplification (Syn.subst σ R) := by simp [amplification]

theorem coefficient_real_lower (z A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] realLower z A B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (coefficient oneCode A)) (fstT (coefficient z B)) := by
  let s := re (GaussianRootAlgebra.sub oneCode (ComplexLogarithmRemainder.scale A oneCode))
  let t := re (GaussianRootAlgebra.sub z (ComplexLogarithmRemainder.scale B oneCode))
  apply RationalArithmetic.order_of_representations _ _ s t A B
    (GaussianEulerIntegrandName.coefficient_represents oneCode A hA).andE₁
    (GaussianEulerIntegrandName.coefficient_represents z B hB).andE₁ hA hB
  let lo := ZT.ofNat B
  let hi := ZT.ofNat A*re z
  let gap := monus (hi.pos+lo.neg) (lo.pos+hi.neg)
  have e : ZT.toZ Γ lo+𝔞(gap) = ZT.toZ Γ hi := zle_toZ h
  apply zle_of_toZ gap
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  simp only [s,t,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
  dsimp only [lo,hi] at e
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
  try ipra_simps
  linear_combination e

theorem multiplier_lower (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (lowerMultiplier A)) (fstT (realMultiplier z B)) := by
  have c := coefficient_real_lower z A B h.andE₁ h.andE₂.andE₁.andE₁ h.andE₂.andE₂
  exact RationalArgmin.rationalLE_congr (GaussianEulerUpperPowerCoefficients.real_multiplier_scalar oneCode A).eqSymm
    (GaussianEulerUpperPowerCoefficients.real_multiplier_scalar z B).eqSymm
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ c c)

theorem real_multiplier_bound (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    bounded (realMultiplier z B) (amplification R) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ one _ one (le_refl one) (le_refl one)
    (le_of_eq_add (d := two) (by unfold amplification GaussianEulerUpperPowerCoefficients.amplification; ipra_ring))
    (GaussianEulerUpperPowerCoefficients.real_multiplier_bound z R B h.andE₂.andE₁)

theorem lower_multiplier_bound (R A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    bounded (lowerMultiplier A) (amplification R) one := by
  have disk : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source oneCode one A := .andI hA
    (le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring)
      (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hA hA)))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ one _ one (le_refl one) (le_refl one)
    (le_of_eq_add (d := two*R) (by unfold amplification GaussianEulerUpperPowerCoefficients.amplification; ipra_ring))
    (GaussianEulerUpperPowerCoefficients.real_multiplier_bound oneCode one A disk)

theorem nonpositive_of_zero_order (r : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE r (natCode zero)) : Γ ⊢[PRAAx]
    le (numeratorOf r).pos (numeratorOf r).neg := by
  let c : PTm n := natCode zero
  let gap := monus (RationalArgmin.left c r) (RationalArgmin.left r c)
  have H := natEq (eq_add_of_le h)
  have Z := ZT.toZ_eq (GaussianRationalSyntheticBounds.natCode_represents (Γ := Γ) zero)
  apply RationalValueBounds.positive_cancel (RationalArgmin.denominator_positive c)
  refine le_of_eq_add (d := gap) ?_
  apply deriveNat
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at Z
  simp only [ZT.toZ] at Z
  simp only [RationalArgmin.left] at H
  dsimp only [gap,c,RationalArgmin.left]
  ipra_simps
  linear_combination H+𝔞(denominatorOf r)*Z

theorem harmonic_sample_nonpositive (p a b : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    le (numeratorOf (fstT (GaussianHarmonicLogarithmName.sample p a b))).pos
      (numeratorOf (fstT (GaussianHarmonicLogarithmName.sample p a b))).neg := by
  have order := GaussianNamedPositiveExponentialOrder.order_at _ _ _ _ p (GaussianHarmonicLogarithmName.below_one_samples a b h)
  have e := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) p (GaussianRationalHorner.qzero : PTm n))).eqTrans
    RationalGaussianRealPart.real_zero
  exact nonpositive_of_zero_order _ (RationalArgmin.rationalLE_congr (.eqRefl _) e order)

theorem original_lower_real_power_multiplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      RationalArgmin.rationalLE (fstT (lowerMultiplier (var 3))) (fstT (realMultiplier (var 0) (var 2)))) :=
  closeUniv 4 (.impI (multiplier_lower _ _ _ _ Prf.hyp0))
theorem actual_harmonic_lower_time_samples_nonpositive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶ le (numeratorOf (fstT (GaussianHarmonicLogarithmName.sample (var 0) (var 1) (var 2)))).pos
      (numeratorOf (fstT (GaussianHarmonicLogarithmName.sample (var 0) (var 1) (var 2)))).neg) :=
  closeUniv 3 (.impI (harmonic_sample_nonpositive _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerCoefficients
