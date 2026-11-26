import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFactor
import IPRADerivations.Analysis.Gamma.GaussianGammaPoleZeros
import IPRADerivations.Analysis.RationalArithmetic.GaussianProductNorm
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianMonicResidualRadius

/-!
# Exact native numerator of the original Barnes base

A Gaussian rational base can be tested for zero by its translated
integer numerator. An integral numerator apart from zero has norm at
least one, which gives a reciprocal denominator for the original base.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalBase

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalFactor (base)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaPoleZeros (poleNumerator translated_pole_numerator)
open GaussianRootAlgebra
  (equal equal_of_values equal_re equal_im equal_refl add_equal re_add im_add re_zero im_zero re_neg im_neg)
open ComplexLogarithmRemainder (normSq zeroCode)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents qzero qadd_canonical qadd_represents represents represents_congr
    canonical_unique zero_represents positive_product)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (bounded_zero_norm)
open GaussianRationalReciprocal (qone_represents_scaled)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem base_represents (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] represents (base z B k) (translated z B k) (B*k) := by
  have hd := positive_product _ _ hB hk
  have h := qadd_represents _ _ _ _ _ hd (qone_represents_scaled (B*k)) (ofGaussian_represents z _ hd)
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) h
  apply equal_of_values <;> simp only [translated,re_add,im_add] <;> ring

theorem base_zero (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] equal (translated z B k) zeroCode) :
    Γ ⊢[PRAAx] base z B k ≐ qzero :=
  canonical_unique _ _ zeroCode (B*k) (qadd_canonical _ _) GaussianRationalSyntheticDivision.qzero_canonical
    (positive_product _ _ hB hk) (represents_congr (.eqRefl _) hz (.eqRefl _) (base_represents z B k hB hk))
    (zero_represents _)

theorem base_zero_iff (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] (((base z B k ≐ qzero) ⟶ equal (translated z B k) zeroCode) ⋏
      (equal (translated z B k) zeroCode ⟶ base z B k ≐ qzero)) := by
  refine .andI (.impI ?_) (.impI (base_zero z B k hB.wk hk.wk Prf.hyp0))
  let Δ := (base z B k ≐ qzero) :: Γ
  have hz : Δ ⊢[PRAAx] base z B k ≐ qzero := Prf.hyp0
  have zeroBound := GaussianMonicResidualRadius.zero_bounded (Γ := Δ) zero one (le_refl one)
  have hb := GaussianRationalReciprocal.bound_congr hz.eqSymm (.eqRefl _) (.eqRefl _) zeroBound
  have eq := bounded_zero_norm _ _ _ _ (positive_product _ _ hB.wk hk.wk) (le_refl one)
    (base_represents z B k hB.wk hk.wk) hb
  have values := GaussianProductNorm.norm_zero_values _ eq
  exact equal_of_values (values.1.trans re_zero.symm) (values.2.trans im_zero.symm)

theorem base_lower (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] le one (normSq (translated z B k))) : Γ ⊢[PRAAx] lower (base z B k) one (B*k) := by
  have hd := positive_product _ _ hB hk
  exact lower_from_representation _ _ _ _ _ hd hd (base_represents z B k hB hk)
    (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl _) hz))

theorem zero_is_negative_integer (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] base z B k ≐ qzero) : Γ ⊢[PRAAx] equal z (poleNumerator B k) := by
  have native := Prf.impE (base_zero_iff z B k hB hk).andE₁ hz
  have hr := equal_re native
  have hi := equal_im native
  apply equal_of_values
  · simp only [translated,re_add,re_zero] at hr
    simp only [poleNumerator,re_neg]
    linear_combination hr
  · simp only [translated,im_add,im_zero] at hi
    simp only [poleNumerator,im_neg]
    linear_combination hi

theorem base_at_negative_integer (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] equal z (poleNumerator B k)) : Γ ⊢[PRAAx] base z B k ≐ qzero :=
  base_zero z B k hB hk
    (GaussianRootAlgebra.equal_trans (add_equal hz (equal_refl _)) (translated_pole_numerator B k))

theorem actual_Barnes_factor_base_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2)) ⟶
      (((base (var 0) (var 1) (var 2) ≐ qzero) ⟶ equal (translated (var 0) (var 1) (var 2)) zeroCode) ⋏
        (equal (translated (var 0) (var 1) (var 2)) zeroCode ⟶ base (var 0) (var 1) (var 2) ≐ qzero))) :=
  closeUniv 3 (.impI (base_zero_iff _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalBase
