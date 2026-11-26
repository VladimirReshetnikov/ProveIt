import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitLogarithmicComposition

/-!
# Uniform actual logarithmic time bounds on a unit-interval compact

For 1/E <= a/b <= 1-1/E, EVERY original harmonic observation of
-log(a/b) is a positive fraction in [1/E,E]. The constants depend only
on the physical compact certificate E, with no raw-denominator bound.
The actual composed outer-log sampler therefore has one uniform disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitCompactTimeBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitLogarithmicMargin (numerator denominator actual_time_fraction)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (a b E : PTm n) : Fm PTm n := GaussianEulerUnitLogarithmicMargin.source a b ⋏
  (le one E ⋏ (le b (E*a) ⋏ le (E*a+b) (E*b)))
def radius (E : PTm n) : PTm n := GaussianCompactLogarithmBounds.radius E E

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (a b E : PTm n) :
    (source a b E).subst σ = source (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) := by simp [source]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (radius E) = radius (Syn.subst σ E) := by simp [radius]

theorem gap_margin (a b E : PTm n) (h : Γ ⊢[PRAAx] source a b E) : Γ ⊢[PRAAx]
    le b (E*LeanProofs.IPRA.PTm.monus b a) := by
  have e := natEq (eq_add_of_le (le_of_lt h.andE₁.andE₂))
  ipra_le sl h.andE₂.andE₂.andE₂ with 𝔞(E)*e

theorem actual_time_lower (p a b E : PTm n) (h : Γ ⊢[PRAAx] source a b E) : Γ ⊢[PRAAx]
    le (denominator p a b) (E*numerator p a b) := by
  have base : Γ ⊢[PRAAx] le (LeanProofs.IPRA.PTm.monus b a*denominator p a b) (b*numerator p a b) :=
    GaussianEulerUnitLogarithmicMargin.finite_margin a b (GaussianEulerUnitLogarithmicMargin.mesh p)
    h.andE₁.andE₁ (le_of_lt h.andE₁.andE₂) (GammaEulerConstantName.mesh_positive _)
  have small := mul_le_mul_right (denominator p a b) (gap_margin a b E h)
  have big := mul_le_mul_right E base
  have clear : Γ ⊢[PRAAx] le (b*denominator p a b) (b*(E*numerator p a b)) :=
    le_trans small (le_congr (by ipra_ring) (by ipra_ring) big)
  exact RationalValueBounds.positive_cancel (le_trans h.andE₁.andE₁ (le_of_lt h.andE₁.andE₂)) clear

theorem actual_time_upper (p a b E : PTm n) (h : Γ ⊢[PRAAx] source a b E) : Γ ⊢[PRAAx]
    le (numerator p a b) (E*denominator p a b) := by
  let v := numerator p a b
  let F := denominator p a b
  let s := ComplexLogarithmRemainder.scale v ComplexLogarithmRemainder.oneCode
  have hf := GaussianEulerUnitLogarithmicMargin.denominator_positive (Γ := Γ) p a b
  have old := GaussianRationalReciprocal.bound_congr (actual_time_fraction p a b (le_of_lt h.andE₁.andE₂)) (.eqRefl _) (.eqRefl _)
    (GaussianUpperTimeLogarithmBound.harmonic_sample_bound p b a h.andE₁.andE₁ (le_of_lt h.andE₁.andE₂))
  have clear := (GaussianRationalMetric.bounded_iff (fraction v F) s F b a hf h.andE₁.andE₁
    (GaussianRationalHorner.ofGaussian_represents s F hf)).iffMp old
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq s ≐ v*v :=
    (ComplexLogarithmRemainder.normSq_scale v ComplexLogarithmRemainder.oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  have native : Γ ⊢[PRAAx] le (a*v) (b*F) := nat_sqrt_mono
    (le_congr ((congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)) (by ipra_ring) clear)
  have bigger := mul_le_mul_right F h.andE₂.andE₂.andE₁
  exact RationalValueBounds.positive_cancel h.andE₁.andE₁
    (le_trans native (le_congr (.eqRefl _) (by ipra_ring) bigger))

theorem evaluated_time_domain (p a b E : PTm n) (h : Γ ⊢[PRAAx] source a b E) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (numerator p a b) (denominator p a b) E E :=
  .andI (.andI (GaussianEulerUnitLogarithmicMargin.numerator_positive p a b h.andE₁)
    (GaussianEulerUnitLogarithmicMargin.denominator_positive p a b))
    (.andI (actual_time_lower p a b E h) (actual_time_upper p a b E h))

theorem original_composition_bound (p a b E : PTm n) (h : Γ ⊢[PRAAx] source a b E) : Γ ⊢[PRAAx]
    bounded (GaussianEulerUnitLogarithmicComposition.sample p a b) (radius E) one :=
  GaussianRationalReciprocal.bound_congr (GaussianEulerUnitLogarithmicComposition.sample_at p a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCompactLogarithmBounds.sample_bound (ConciseIPRA.PTm.succ p) _ _ E E h.andE₂.andE₁
      (evaluated_time_domain (GaussianEulerUnitLogarithmicComposition.query p b) a b E h))

theorem actual_unit_compact_time_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ GaussianCompactLogarithmBounds.domain
      (numerator (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2)) (var 3) (var 3)) :=
  closeUniv 4 (.impI (evaluated_time_domain _ _ _ _ Prf.hyp0))

theorem actual_unit_compact_outer_log_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ bounded (GaussianEulerUnitLogarithmicComposition.sample (var 0) (var 1) (var 2)) (radius (var 3)) one) :=
  closeUniv 4 (.impI (original_composition_bound _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitCompactTimeBounds
