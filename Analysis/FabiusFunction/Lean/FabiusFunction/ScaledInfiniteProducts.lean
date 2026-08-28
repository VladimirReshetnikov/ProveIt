import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Infinite products at summable scales

This module isolates the common convergence mechanism behind products such as
the dyadically scaled sinc product.  Let `a n` be scalar scales whose norms are
summable, and let a factor `f` satisfy

`f(z) - 1 = O(z)` as `z → 0`.

Then the product `∏' n, f (a n • z)` converges uniformly on every compact
set.  In a locally compact domain it consequently converges locally uniformly.
The result is deliberately independent of the Fabius function and of the
particular choice of scales.

The principal results are:

* `summable_norm_scaled_sub_one`: absolute summability of the factor
  deviations at each point;
* `hasProdUniformlyOn_scaled`: compact-uniform convergence to the pointwise
  infinite product;
* `hasProdLocallyUniformly_scaled`: locally uniform convergence on the whole
  domain;
* `continuous_tprod_scaled`: continuity of the product;
* `differentiable_tprod_scaled` and
  `differentiable_tprod_scaled_of_eq_one`: the Banach-algebra-valued
  holomorphic versions;
* `tprod_scaled_ne_zero` and `tprod_scaled_eq_zero_iff`: no hidden zero can
  occur when no factor vanishes.
-/

set_option autoImplicit false

open Asymptotics Filter Set Topology

namespace Fabius

noncomputable section

section Pointwise

variable { 𝕜 E R : Type* }
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedRing R]

/-- If the scale norms are summable and `f - 1` is at most linear near the
origin, then the deviations of the scaled factors from one are summable at
each point. -/
theorem summable_norm_scaled_sub_one (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hf : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z)) (z : E) :
    Summable fun n ↦ ‖f (a n • z) - 1‖ := by
  apply hf.comp_summable_norm
  exact (ha.mul_right ‖z‖).of_nonneg_of_le
    (fun n ↦ norm_nonneg (a n • z)) (fun n ↦ norm_smul_le (a n) z)

end Pointwise

section Uniform

variable { 𝕜 E R : Type* }
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

/-- **Compact-uniform scaled-product criterion.**  If `∑ n, ‖a n‖`
converges, `f` is continuous, and `f(z) - 1 = O(z)` at the origin, then the
products of the factors `f (a n • z)` converge uniformly on every prescribed
compact set to their pointwise infinite product. -/
theorem hasProdUniformlyOn_scaled (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (hf : Continuous f) {K : Set E} (hK : IsCompact K) :
    HasProdUniformlyOn (fun n z ↦ f (a n • z))
      (fun z ↦ ∏' n, f (a n • z)) K := by
  obtain ⟨c, hc, hcO⟩ := hfO.exists_nonneg
  obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhds_iff.mp hcO.bound
  obtain ⟨B, hB, hKB⟩ := hK.isBounded.exists_pos_norm_le
  have ha0 : Tendsto (fun n ↦ ‖a n‖) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ha.tendsto_cofinite_zero
  have hasmall : ∀ᶠ n in atTop, ‖a n‖ < δ / B :=
    ha0.eventually_lt_const (div_pos hδ hB)
  have hmajor : ∀ᶠ n in atTop, ∀ z ∈ K,
      ‖-1 + f (a n • z)‖ ≤ (c * B) * ‖a n‖ := by
    filter_upwards [hasmall] with n hn
    intro z hz
    have harg : a n • z ∈ Metric.ball (0 : E) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      calc
        ‖a n • z‖ ≤ ‖a n‖ * ‖z‖ := norm_smul_le (a n) z
        _ ≤ ‖a n‖ * B :=
          mul_le_mul_of_nonneg_left (hKB z hz) (norm_nonneg (a n))
        _ < δ := (lt_div_iff₀ hB).mp hn
    have hlocal : ‖-1 + f (a n • z)‖ ≤ c * ‖a n • z‖ := by
      have hbound : ‖f (a n • z) - 1‖ ≤ c * ‖a n • z‖ := hδO harg
      simpa only [sub_eq_add_neg, add_comm] using hbound
    calc
      ‖-1 + f (a n • z)‖ ≤ c * ‖a n • z‖ := hlocal
      _ ≤ c * (‖a n‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (norm_smul_le (a n) z) hc
      _ ≤ c * (‖a n‖ * B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hKB z hz) (norm_nonneg (a n))) hc
      _ = (c * B) * ‖a n‖ := by ring
  have hprod := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun n z ↦ -1 + f (a n • z)) hK (ha.mul_left (c * B))
    hmajor (fun n ↦
      (continuous_const.add
        (hf.comp (continuous_const_smul (a n)))).continuousOn)
  simpa only [add_neg_cancel_left] using hprod

/-- The factors in `hasProdUniformlyOn_scaled` are multipliable uniformly on
each compact set. -/
theorem multipliableUniformlyOn_scaled (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (hf : Continuous f) {K : Set E} (hK : IsCompact K) :
    MultipliableUniformlyOn (fun n z ↦ f (a n • z)) K :=
  (hasProdUniformlyOn_scaled f a ha hfO hf hK).multipliableUniformlyOn

section LocallyCompact

variable [LocallyCompactSpace E]

/-- Under local compactness of the domain, the scaled product converges
locally uniformly everywhere. -/
theorem hasProdLocallyUniformly_scaled (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (hf : Continuous f) :
    HasProdLocallyUniformly (fun n z ↦ f (a n • z))
      (fun z ↦ ∏' n, f (a n • z)) := by
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  exact hasProdUniformlyOn_scaled f a ha hfO hf hK

/-- The locally uniform scaled product is locally uniformly multipliable. -/
theorem multipliableLocallyUniformly_scaled (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (hf : Continuous f) :
    MultipliableLocallyUniformly (fun n z ↦ f (a n • z)) :=
  (hasProdLocallyUniformly_scaled f a ha hfO hf).multipliableLocallyUniformly

/-- The locally uniform scaled infinite product is continuous. -/
theorem continuous_tprod_scaled (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (hf : Continuous f) :
    Continuous (fun z ↦ ∏' n, f (a n • z)) := by
  apply (hasProdLocallyUniformly_scaled f a ha hfO hf).continuous
  exact (Filter.Eventually.of_forall fun s ↦
    continuous_finsetProd s fun n _ ↦
      hf.comp (continuous_const_smul (a n))).frequently

end LocallyCompact

end Uniform

section Holomorphic

variable {A : Type*}
variable [NormedCommRing A] [NormOneClass A] [NormedAlgebra ℂ A]
variable [CompleteSpace A]

/-- **Weierstrass theorem for scaled products.**  A complex-differentiable
factor with a linear deviation from one at the origin produces an everywhere
complex-differentiable, Banach-algebra-valued infinite product at every
summable family of complex scales. -/
theorem differentiable_tprod_scaled (f : ℂ → A) (a : ℕ → ℂ)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : ℂ ↦ z))
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z ↦ ∏' n, f (a n • z)) := by
  rw [← differentiableOn_univ]
  have hconv :=
    HasProdLocallyUniformly.hasProdLocallyUniformlyOn
      (hasProdLocallyUniformly_scaled f a ha hfO hf.continuous)
      (s := Set.univ)
  exact hconv.differentiableOn
      (Filter.Eventually.of_forall fun s ↦ by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finsetProd (u := s) (fun _ _ ↦ by fun_prop))
      isOpen_univ

/-- A differentiable factor normalized by `f 0 = 1` automatically satisfies
the linear-deviation hypothesis, so its product at any summable complex
scales is entire. -/
theorem differentiable_tprod_scaled_of_eq_one (f : ℂ → A) (a : ℕ → ℂ)
    (ha : Summable fun n ↦ ‖a n‖) (hf : Differentiable ℂ f)
    (hf0 : f 0 = 1) :
    Differentiable ℂ (fun z ↦ ∏' n, f (a n • z)) := by
  apply differentiable_tprod_scaled f a ha
  · simpa only [hf0, sub_self, sub_zero] using (hf 0).isBigO_sub
  · exact hf

end Holomorphic

section Nonvanishing

variable { 𝕜 E R : Type* }
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [NormMulClass R]

/-- **No hidden zeros.**  Absolute summability of the factor deviations rules
out a zero of the infinite product unless one of its factors already
vanishes. -/
theorem tprod_scaled_ne_zero (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (z : E) (hz : ∀ n, f (a n • z) ≠ 0) :
    ∏' n, f (a n • z) ≠ 0 := by
  have hsum : Summable fun n ↦ ‖-1 + f (a n • z)‖ := by
    simpa only [sub_eq_add_neg, add_comm] using
      summable_norm_scaled_sub_one f a ha hfO z
  have hne : ∀ n, 1 + (-1 + f (a n • z)) ≠ 0 := by
    simpa only [add_neg_cancel_left] using hz
  simpa only [add_neg_cancel_left] using
    tprod_one_add_ne_zero_of_summable hne hsum

/-- A scaled infinite product vanishes exactly when one of its factors
vanishes.  The forward implication is the substantive no-hidden-zero result;
the reverse implication uses Mathlib's total infinite-product convention. -/
theorem tprod_scaled_eq_zero_iff (f : E → R) (a : ℕ → 𝕜)
    (ha : Summable fun n ↦ ‖a n‖)
    (hfO : (fun z ↦ f z - 1) =O[𝓝 0] (fun z : E ↦ z))
    (z : E) :
    (∏' n, f (a n • z)) = 0 ↔ ∃ n, f (a n • z) = 0 := by
  constructor
  · intro hzero
    by_contra hfactor
    have hfactor' : ∀ n, f (a n • z) ≠ 0 := by
      intro n hn
      exact hfactor ⟨n, hn⟩
    exact (tprod_scaled_ne_zero f a ha hfO z hfactor') hzero
  · exact tprod_of_exists_eq_zero

end Nonvanishing

end

end Fabius
