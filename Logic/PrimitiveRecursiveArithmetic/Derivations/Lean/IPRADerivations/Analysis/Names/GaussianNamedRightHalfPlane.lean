import IPRADerivations.Analysis.RationalArithmetic.RationalUpperRepresentation
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport
import IPRADerivations.Analysis.Names.GaussianNameBounds
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerPowerCoefficients

/-!
# Native rational inputs sampled from a named right-half-plane input

The positive real-part certificate is the existing actual named real
order: the constant 1/A lies below the given fixed Gaussian name.
Finite real-order gap removal retains the actual sample's one dyadic
error. At computed late precisions that sample therefore has native
real part at least 1/(2A). Its native numerator/denominator are decoded
from the SAME original raw sample, and the original point CN supplies
its computed uniform disk. No sampled margin or disk is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlane

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderTransport (upperSlack remove_upper_slack)
open RationalValueBounds (upper upper_congr)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (oneCode re)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def marginPoint (A : PTm n) : PTm n := ofGaussian oneCode A
def certificate (f : PR 2) (x A : PTm n) : Fm PTm n := realOrder constantF f (marginPoint A) x
def source (f : PR 2) (x A : PTm n) : Fm PTm n := pointCN f x ⋏ (le one A ⋏ certificate f x A)
def numerator (f : PR 2) (p x : PTm n) : PTm n := rawGaussian (ap2 f p x)
def denominator (f : PR 2) (p x : PTm n) : PTm n := rawDen (ap2 f p x)
def radius (f : PR 2) (x : PTm n) : PTm n := GaussianNameBounds.U f x
def precision (p A : PTm n) : PTm n := GaussianFastValueCut.exponent (two*A) p
def threshold (A : PTm n) : PTm n := precision zero A
@[simp] theorem subst_marginPoint {l : ℕ} (σ : Fin n → PTm l) (A : PTm n) :
    Syn.subst σ (marginPoint A) = marginPoint (Syn.subst σ A) := by simp [marginPoint,oneCode,ComplexLogarithmRemainder.code,ZT.ofNat]
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x A : PTm n) :
    (certificate f x A).subst σ = certificate f (Syn.subst σ x) (Syn.subst σ A) := by simp [certificate]
@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x A : PTm n) :
    (source f x A).subst σ = source f (Syn.subst σ x) (Syn.subst σ A) := by simp [source]
@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (numerator f p x) = numerator f (Syn.subst σ p) (Syn.subst σ x) := by simp [numerator]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (denominator f p x) = denominator f (Syn.subst σ p) (Syn.subst σ x) := by simp [denominator]
@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x : PTm n) :
    Syn.subst σ (radius f x) = radius f (Syn.subst σ x) := by simp [radius]
@[simp] theorem subst_precision {l : ℕ} (σ : Fin n → PTm l) (p A : PTm n) :
    Syn.subst σ (precision p A) = precision (Syn.subst σ p) (Syn.subst σ A) := by simp [precision]
@[simp] theorem subst_threshold {l : ℕ} (σ : Fin n → PTm l) (A : PTm n) :
    Syn.subst σ (threshold A) = threshold (Syn.subst σ A) := by simp [threshold]

theorem source_upper_slack (f : PR 2) (x A p t : PTm n) (h : Γ ⊢[PRAAx] certificate f x A) : Γ ⊢[PRAAx]
    upperSlack (fstT (marginPoint A)) (fstT (ap2 f p x)) one (unit p) one t :=
  upper_congr (congrFst (constant_at t (marginPoint A))) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (real_order_at constantF f (marginPoint A) x t p h)

theorem actual_sample_upper (f : PR 2) (x A p : PTm n) (h : Γ ⊢[PRAAx] certificate f x A) : Γ ⊢[PRAAx]
    upper (fstT (marginPoint A)) (fstT (ap2 f p x)) one (unit p) :=
  remove_upper_slack _ _ _ _ one
    (source_upper_slack f x A p (GaussianNamedRealOrderTransport.precision (fstT (marginPoint A)) (fstT (ap2 f p x)) (unit p) one) h)

theorem half_margin_from_upper (q A U : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hU : Γ ⊢[PRAAx] le one U) (hLate : Γ ⊢[PRAAx] le (two*A) U)
    (h : Γ ⊢[PRAAx] upper (fstT (marginPoint A)) (fstT q) one U) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.realLower (rawGaussian q) (two*A) (rawDen q) := by
  let B := rawDen q
  let v := re (rawGaussian q)
  have clear := RationalUpperRepresentation.upper_from_representations _ _ A B one U (re oneCode) v
    (ofGaussian_represents oneCode A hA).andE₁ (raw_represents q).andE₁ h
  let left := ZT.ofNat (U*B)
  let right := ZT.ofNat (U*A)*v+ZT.ofNat (A*B)
  have margin : Γ ⊢[PRAAx] zle left right :=
    PolynomialBisection.zle_congr (by dsimp only [left]; simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]; ring)
      (by dsimp only [right]; simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]; ipra_simps; ring) clear
  have em := zle_toZ margin
  have el := natEq (eq_add_of_le hLate)
  apply PolynomialBisection.zle_scale_cancel (c := U) hU
  apply zle_of_toZ (two*PolynomialBisection.slack left right+monus U (two*A)*B)
  dsimp only [PolynomialBisection.slack,left,right]
  dsimp only [left,right] at em
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at em ⊢
  ipra_simps
  linear_combination 2*em - 𝔞 B*el

theorem precision_budget (p A : PTm n) : Γ ⊢[PRAAx] le (two*A) (unit (precision p A)) :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*A) (unit_positive p)))
    (GaussianFastValueCut.query_budget _ _)
theorem threshold_budget (p A : PTm n) (h : Γ ⊢[PRAAx] le (threshold A) p) : Γ ⊢[PRAAx] le (two*A) (unit p) :=
  le_trans (precision_budget zero A) (GaussianExponentialReference.unit_monotone h)

theorem actual_late_margin (f : PR 2) (x A p : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hLate : Γ ⊢[PRAAx] le (threshold A) p) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.realLower (numerator f p x) (two*A) (denominator f p x) :=
  half_margin_from_upper _ A (unit p) h.andE₂.andE₁ (unit_positive p) (threshold_budget p A hLate)
    (actual_sample_upper f x A p h.andE₂.andE₂)

theorem actual_sample_disk (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (numerator f p x) (radius f x*denominator f p x) :=
  le_congr (by unfold numerator; ipra_ring) (by unfold radius denominator; ipra_ring)
    ((GaussianRationalMetric.bounded_iff _ _ _ _ _ (raw_den_positive _) (le_refl one) (raw_represents _)).iffMp
      (GaussianNameBounds.sample_bound f x p h))

theorem actual_late_source (f : PR 2) (x A p : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hLate : Γ ⊢[PRAAx] le (threshold A) p) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source (numerator f p x) (radius f x) (denominator f p x) (two*A) :=
  .andI (positive_product _ _ (le_succ_self one) h.andE₂.andE₁)
    (.andI (.andI (raw_den_positive _) (actual_sample_disk f x p h.andE₁)) (actual_late_margin f x A p h hLate))

theorem actual_retimed_source (f : PR 2) (x A p : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source (numerator f (precision p A) x) (radius f x)
      (denominator f (precision p A) x) (two*A) :=
  .andI (positive_product _ _ (le_succ_self one) h.andE₂.andE₁)
    (.andI (.andI (raw_den_positive _) (actual_sample_disk f x (precision p A) h.andE₁))
      (half_margin_from_upper _ A (unit (precision p A)) h.andE₂.andE₁ (unit_positive _) (precision_budget p A)
        (actual_sample_upper f x A (precision p A) h.andE₂.andE₂)))

theorem actual_native_point_distance (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ofGaussian (numerator f p x) (denominator f p x)) (ap2 f p x) zero one :=
  GaussianFastValueCut.recode_distance _

theorem original_named_half_plane_late_native_Euler_source_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((source f (var 0) (var 1) ⋏ le (threshold (var 1)) (var 2)) ⟶
        GaussianEulerLowerPowerCoefficients.source (numerator f (var 2) (var 0)) (radius f (var 0))
          (denominator f (var 2) (var 0)) (two*var 1)) :=
  closeUniv 3 (.impI (actual_late_source f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_named_half_plane_computed_native_Euler_source_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶
        GaussianEulerLowerPowerCoefficients.source (numerator f (precision (var 2) (var 1)) (var 0)) (radius f (var 0))
          (denominator f (precision (var 2) (var 1)) (var 0)) (two*var 1)) :=
  closeUniv 3 (.impI (actual_retimed_source f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlane
