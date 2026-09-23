import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.LinearCombination

/-!
# Continuum many independent defect vectors of the harmonic diagonal operator

This file formalizes `ihs:hh:lem:continuum` of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex`, together with the
facts about the operator `D` stated just before it in `ihs:hh:sec:largecoker`.

## Index convention

The source works on `H = ℓ²(ℕ_{≥1})` with `D e_n = n⁻¹ e_n`. Here `H` is `ℓ²(ℕ, ℂ)` and the
source index `n ≥ 1` is the Lean index `n - 1`, so the Lean coordinate `n` carries the weight
`(n + 1)⁻¹`: `(invDiag x) n = x n / (n + 1)` (`invDiag_apply`) and
`invDiag e_n = (n + 1)⁻¹ e_n` for the standard basis vector `e_n = lp.single 2 n 1`
(`invDiag_single`). Likewise the source vector `f^(r) = (n^(-r))_{n ≥ 1}` is
`powerVec r`, whose Lean coordinate `n` is `(n + 1)^(-r)` (`powerVec_apply`).

## Main results

* The operator `D` (`invDiag`) is a bounded operator of norm at most `1`
  (`norm_invDiag_apply_le`, `opNorm_invDiag_le`), positive (`isPositive_invDiag`; also
  positive definite, `re_inner_invDiag_self_pos`, from the coordinatewise formula
  `re ⟪D x, x⟫ = ∑ₙ ‖x_n‖² / (n + 1)`, `hasSum_re_inner_invDiag_self`),
  self-adjoint (`isSelfAdjoint_invDiag`) and injective (`invDiag_injective`). A vector `x`
  lies in `Ran D` exactly when `((n + 1) x_n)_n ∈ ℓ²` (`mem_range_invDiag_iff`). The operator is
  not onto: the harmonic vector `f^(1) = (n⁻¹)_{n ≥ 1}` has no preimage
  (`powerVec_one_notMem_range_invDiag`, `not_surjective_invDiag`).
* `ihs:hh:lem:continuum`: for `r ∈ (1/2, 3/2]` the vectors `f^(r)` lie in `ℓ²`
  (`memℓp_powerSeq`, valid for every `r > 1/2`), and their classes in `H / Ran D` are linearly
  independent over `ℂ` (`linearIndependent_powerVec_mkQ`; hence so are the vectors themselves,
  `linearIndependent_powerVec`, and none of them lies in `Ran D`,
  `powerVec_notMem_range_invDiag`). The analytic core is
  `not_summable_norm_mul_sum_sq`: for finitely many distinct exponents `r_j ≤ 3/2` and
  coefficients not all zero, `(n g_n)_n ∉ ℓ²` for `g = ∑ c_j f^(r_j)`, proved through the
  asymptotics `n g_n = c_1 n^(1 - r_1) (1 + o(1))` of the source. Since `(1/2, 3/2]` has the
  cardinality of the continuum, `dim_ℂ (H / Ran D) ≥ 2^ℵ₀`
  (`continuum_le_rank_quotient_range_invDiag`).
* The step of the proof of `ihs:hh:thm:continuum` that passes to `D²`: since
  `Ran D² ⊆ Ran D`, the same classes are independent modulo `Ran D²`
  (`linearIndependent_powerVec_mkQ_sq`, `continuum_le_rank_quotient_range_invDiag_sq`).

## Pending

`ihs:hh:thm:continuum` itself (the bound `dim_K coker(D + E) ≥ 2^ℵ₀` on `H((t^Γ))` for every
positive-order `E`, and the same with leading operator `D²`) is not formalized here: it combines
the results above with `ihs:hh:cor:independent`, which is not yet formalized in the project.
-/

namespace Surreal.ContinuumDefects

open Filter Topology
open scoped ENNReal lp ComplexConjugate

noncomputable section

section Preliminaries

/-- Membership of a complex sequence in `ℓ²`, with the exponent written as a natural power. -/
theorem memℓp_two_iff_summable_sq (f : ℕ → ℂ) :
    Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp, ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]

/-- The complex number `n + 1` has norm `n + 1`. -/
theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  exact_mod_cast Complex.norm_natCast (n + 1)

end Preliminaries

section Operator

/-- For `x ∈ ℓ²`, the sequence `x_n / (n + 1)` is again in `ℓ²`. -/
theorem memℓp_invDiag (x : ℓ²(ℕ, ℂ)) : Memℓp (fun n : ℕ => x n / ((n : ℂ) + 1)) 2 := by
  rw [memℓp_two_iff_summable_sq]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((memℓp_two_iff_summable_sq x).mp (lp.memℓp x))
  have h1 : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [norm_natCast_add_one]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : ‖x n / ((n : ℂ) + 1)‖ ≤ ‖x n‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) h1
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

/-- The diagonal operator `D` of `ihs:hh:sec:largecoker` as a linear map. -/
def invDiagLinear : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun x := ⟨fun n => x n / ((n : ℂ) + 1), memℓp_invDiag x⟩
  map_add' x y := lp.ext (funext fun n => by
    simp only [lp.coeFn_add, Pi.add_apply, add_div])
  map_smul' c x := lp.ext (funext fun n => by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc])

/-- `D` does not increase the `ℓ²` norm. -/
theorem norm_invDiagLinear_le (x : ℓ²(ℕ, ℂ)) : ‖invDiagLinear x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (norm_nonneg x) ?_
  rw [lp.norm_rpow_eq_tsum hp x]
  refine Summable.tsum_le_tsum (fun n => ?_) ((memℓp_gen_iff hp).mp (lp.memℓp _))
    ((memℓp_gen_iff hp).mp (lp.memℓp x))
  have h1 : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [norm_natCast_add_one]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : ‖x n / ((n : ℂ) + 1)‖ ≤ ‖x n‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) h1
  exact Real.rpow_le_rpow (norm_nonneg _) h2 hp.le

/-- The bounded diagonal operator `D e_n = n⁻¹ e_n` of `ihs:hh:sec:largecoker`, on
`ℓ²(ℕ, ℂ)` with the source index `n ≥ 1` shifted to `n - 1`. -/
def invDiag : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  invDiagLinear.mkContinuous 1 fun x => by
    rw [one_mul]
    exact norm_invDiagLinear_le x

/-- `(D x)_n = x_n / (n + 1)` in the shifted indexing. -/
theorem invDiag_apply (x : ℓ²(ℕ, ℂ)) (n : ℕ) : invDiag x n = x n / ((n : ℂ) + 1) :=
  rfl

/-- `D e_n = n⁻¹ e_n` in the shifted indexing: `D e_n = (n + 1)⁻¹ e_n`. -/
theorem invDiag_single (n : ℕ) :
    invDiag (lp.single 2 n (1 : ℂ)) = ((n : ℂ) + 1)⁻¹ • lp.single 2 n (1 : ℂ) := by
  refine lp.ext (funext fun m => ?_)
  rw [invDiag_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply,
    smul_eq_mul]
  by_cases hm : m = n
  · subst hm
    simp only [if_pos, one_div, mul_one]
  · simp only [if_neg hm, zero_div, mul_zero]

/-- `D` is bounded: it does not increase the norm. -/
theorem norm_invDiag_apply_le (x : ℓ²(ℕ, ℂ)) : ‖invDiag x‖ ≤ ‖x‖ :=
  norm_invDiagLinear_le x

/-- `D` is bounded with operator norm at most `1`. -/
theorem opNorm_invDiag_le : ‖invDiag‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Coordinatewise symmetry of `D`: `⟪a / (n + 1), b⟫ = ⟪a, b / (n + 1)⟫`. -/
theorem inner_invDiag_coord (a b : ℂ) (n : ℕ) :
    inner ℂ (a / ((n : ℂ) + 1)) b = inner ℂ a (b / ((n : ℂ) + 1)) := by
  rw [RCLike.inner_apply', RCLike.inner_apply', map_div₀, map_add, map_natCast, map_one,
    div_mul_eq_mul_div, mul_div_assoc]

/-- The quadratic form of `D` coordinatewise: `re ⟪D x, x⟫ = ∑ₙ ‖x_n‖² / (n + 1)`. -/
theorem hasSum_re_inner_invDiag_self (x : ℓ²(ℕ, ℂ)) :
    HasSum (fun n : ℕ => ‖x n‖ ^ 2 / ((n : ℝ) + 1)) (RCLike.re (inner ℂ (invDiag x) x)) := by
  have hs := Complex.hasSum_re (lp.hasSum_inner (invDiag x) x)
  have hf : (fun n : ℕ => ‖x n‖ ^ 2 / ((n : ℝ) + 1)) =
      fun n : ℕ => (inner ℂ (invDiag x n) (x n)).re := by
    funext n
    have h : inner ℂ (invDiag x n) (x n) =
        (((‖x n‖ ^ 2 / ((n : ℝ) + 1) : ℝ)) : ℂ) := by
      rw [invDiag_apply, RCLike.inner_apply', map_div₀, div_mul_eq_mul_div, Complex.conj_mul',
        map_add, map_natCast, map_one]
      push_cast
      ring
    rw [h, Complex.ofReal_re]
  rw [hf]
  exact hs

/-- `ihs:hh:sec:largecoker`: `D` is positive, that is, symmetric with `re ⟪D x, x⟫ ≥ 0`. -/
theorem isPositive_invDiag : invDiag.IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · change inner ℂ (invDiag x) y = inner ℂ x (invDiag y)
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact tsum_congr fun n => inner_invDiag_coord (x n) (y n) n
  · change 0 ≤ RCLike.re (inner ℂ (invDiag x) x)
    exact (hasSum_re_inner_invDiag_self x).nonneg fun n => by positivity

/-- `ihs:hh:sec:largecoker`, positive definite reading: `re ⟪D x, x⟫ > 0` for `x ≠ 0`. -/
theorem re_inner_invDiag_self_pos {x : ℓ²(ℕ, ℂ)} (hx : x ≠ 0) :
    0 < RCLike.re (inner ℂ (invDiag x) x) := by
  obtain ⟨n, hn⟩ : ∃ n, x n ≠ 0 := by
    by_contra! h
    exact hx (lp.ext (funext fun n => by simpa using h n))
  have hs := hasSum_re_inner_invDiag_self x
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun m => by positivity) n
    (div_pos (pow_pos (norm_pos_iff.mpr hn) 2) (by positivity))

/-- `ihs:hh:sec:largecoker`: `D` is self-adjoint. -/
theorem isSelfAdjoint_invDiag : IsSelfAdjoint invDiag :=
  isPositive_invDiag.isSelfAdjoint

/-- `ihs:hh:sec:largecoker`: `D` is injective. -/
theorem invDiag_injective : Function.Injective invDiag := by
  intro x y h
  refine lp.ext (funext fun n => ?_)
  have h1 := congrArg (fun z : ℓ²(ℕ, ℂ) => z n) h
  simp only [invDiag_apply] at h1
  exact (div_left_inj' (Nat.cast_add_one_ne_zero n)).mp h1

/-- A vector lies in `Ran D` exactly when `((n + 1) x_n)_n` is square summable, which is the
source's criterion `(n g_n) ∈ ℓ²` in the shifted indexing. -/
theorem mem_range_invDiag_iff (x : ℓ²(ℕ, ℂ)) :
    x ∈ LinearMap.range invDiag.toLinearMap ↔ Memℓp (fun n : ℕ => ((n : ℂ) + 1) * x n) 2 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    convert lp.memℓp y using 1
    funext n
    exact mul_div_cancel₀ _ (Nat.cast_add_one_ne_zero n)
  · intro h
    refine LinearMap.mem_range.mpr ⟨⟨_, h⟩, lp.ext (funext fun n => ?_)⟩
    change ((n : ℂ) + 1) * x n / ((n : ℂ) + 1) = x n
    rw [mul_div_cancel_left₀ _ (Nat.cast_add_one_ne_zero n)]

end Operator

section PowerVectors

/-- The sequence `((n + 1)^(-r))_n`, the source's `f^(r) = (n^(-r))_{n ≥ 1}`, is square
summable for `r > 1/2`. -/
theorem memℓp_powerSeq {r : ℝ} (hr : 1 / 2 < r) :
    Memℓp (fun n : ℕ => ((((n : ℝ) + 1) ^ (-r) : ℝ) : ℂ)) 2 := by
  rw [memℓp_two_iff_summable_sq]
  have hs := (Real.summable_one_div_nat_add_rpow 1 (2 * r)).mpr (by linarith)
  refine hs.congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn _),
    abs_of_nonneg hn, one_div, ← Real.rpow_neg hn, ← Real.rpow_mul_natCast hn]
  congr 1
  push_cast
  ring

/-- The defect vector `f^(r) = (n^(-r))_{n ≥ 1}` of `ihs:hh:lem:continuum`, for `r > 1/2`, in
the shifted indexing. -/
def powerVec (r : ℝ) (hr : 1 / 2 < r) : ℓ²(ℕ, ℂ) :=
  ⟨fun n : ℕ => ((((n : ℝ) + 1) ^ (-r) : ℝ) : ℂ), memℓp_powerSeq hr⟩

/-- The Lean coordinate `n` (source index `n + 1`) of `f^(r)` is `(n + 1)^(-r)`. -/
theorem powerVec_apply (r : ℝ) (hr : 1 / 2 < r) (n : ℕ) :
    powerVec r hr n = ((((n : ℝ) + 1) ^ (-r) : ℝ) : ℂ) :=
  rfl

/-- The analytic core of `ihs:hh:lem:continuum`. Let `g_n = ∑_j c_j (n + 1)^(-r_j)` for finitely
many distinct exponents `r_j ≤ 3/2` and coefficients `c_j` that are not all zero. Then
`((n + 1) g_n)_n` is not square summable. With `r_1` the least exponent carrying a nonzero
coefficient, `(n + 1) g_n = c_1 (n + 1)^(1 - r_1) (1 + o(1))`, so its squared modulus is
eventually at least `(|c_1| / 2)² (n + 1)⁻¹`. -/
theorem not_summable_norm_mul_sum_sq {ι : Type*} (t : Finset ι) (ρ : ι → ℝ)
    (hρ : Set.InjOn ρ t) (hle : ∀ i ∈ t, ρ i ≤ 3 / 2) (c : ι → ℂ) (hc : ∃ i ∈ t, c i ≠ 0) :
    ¬ Summable fun n : ℕ =>
      ‖((n : ℂ) + 1) * ∑ i ∈ t, c i * ((((n : ℝ) + 1) ^ (-ρ i) : ℝ) : ℂ)‖ ^ 2 := by
  classical
  intro hsum
  -- the least exponent `r₁ = ρ i₁` among the nonzero coefficients
  have ht' : (t.filter fun i => c i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hci⟩ := hc
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨i₁, hi₁, hmin⟩ := (t.filter fun i => c i ≠ 0).exists_min_image ρ ht'
  rw [Finset.mem_filter] at hi₁
  -- the normalized sums `h n = ∑ c_i (n + 1)^(r₁ - ρ i)` tend to `c i₁`
  let h : ℕ → ℂ := fun n => ∑ i ∈ t, c i * ((((n : ℝ) + 1) ^ (ρ i₁ - ρ i) : ℝ) : ℂ)
  have hX : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have htend : Tendsto h atTop (𝓝 (∑ i ∈ t, if i = i₁ then c i else 0)) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    by_cases hii : i = i₁
    · subst hii
      simp only [sub_self, Real.rpow_zero, Complex.ofReal_one, mul_one, if_pos]
      exact tendsto_const_nhds
    · rw [if_neg hii]
      by_cases hci : c i = 0
      · simp only [hci, zero_mul]
        exact tendsto_const_nhds
      · have hlt : ρ i₁ < ρ i := lt_of_le_of_ne (hmin i (Finset.mem_filter.mpr ⟨hi, hci⟩))
          fun heq => hii (hρ hi hi₁.1 heq.symm)
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (ρ i₁ - ρ i)) atTop (𝓝 0) := by
          have h2 := (tendsto_rpow_neg_atTop (sub_pos.mpr hlt)).comp hX
          rwa [neg_sub] at h2
        have h3 : Tendsto (fun n : ℕ => ((((n : ℝ) + 1) ^ (ρ i₁ - ρ i) : ℝ) : ℂ)) atTop
            (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp h1
        rw [Complex.ofReal_zero] at h3
        have h4 := (tendsto_const_nhds (x := c i)).mul h3
        rwa [mul_zero] at h4
  rw [Finset.sum_ite_eq' t i₁ c, if_pos hi₁.1] at htend
  have hc₁ : 0 < ‖c i₁‖ := norm_pos_iff.mpr hi₁.2
  have hev : ∀ᶠ n in atTop, ‖c i₁‖ / 2 ≤ ‖h n‖ :=
    htend.norm.eventually_const_le (by linarith)
  -- the lower bound `(|c₁| / 2)² (n + 1)⁻¹ ≤ |(n + 1) g_n|²`
  have hbound : ∀ᶠ n : ℕ in atTop, ‖(‖c i₁‖ / 2) ^ 2 * ((n : ℝ) + 1)⁻¹‖ ≤
      ‖((n : ℂ) + 1) * ∑ i ∈ t, c i * ((((n : ℝ) + 1) ^ (-ρ i) : ℝ) : ℂ)‖ ^ 2 := by
    filter_upwards [hev] with n hn
    have hX0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hX1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hfac : ((n : ℂ) + 1) * ∑ i ∈ t, c i * ((((n : ℝ) + 1) ^ (-ρ i) : ℝ) : ℂ) =
        ((((n : ℝ) + 1) ^ (1 - ρ i₁) : ℝ) : ℂ) * h n := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hpow : ((n : ℝ) + 1) ^ (1 - ρ i₁) * ((n : ℝ) + 1) ^ (ρ i₁ - ρ i) =
          ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-ρ i) := by
        rw [← Real.rpow_add hX0, show 1 - ρ i₁ + (ρ i₁ - ρ i) = 1 + -ρ i by ring,
          Real.rpow_add hX0, Real.rpow_one]
      have hpowC := congrArg (fun a : ℝ => (a : ℂ)) hpow
      push_cast at hpowC
      linear_combination (c i) * hpowC.symm
    have hle1 : ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ ((n : ℝ) + 1) ^ (1 - ρ i₁) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [hle i₁ hi₁.1])
    have hsq : (((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ 2 = ((n : ℝ) + 1)⁻¹ := by
      rw [← Real.rpow_mul_natCast hX0.le, ← Real.rpow_neg_one]
      congr 1
      norm_num
    have hL : ‖(‖c i₁‖ / 2) ^ 2 * ((n : ℝ) + 1)⁻¹‖ = (‖c i₁‖ / 2) ^ 2 * ((n : ℝ) + 1)⁻¹ :=
      Real.norm_of_nonneg (by positivity)
    have hR : ‖((((n : ℝ) + 1) ^ (1 - ρ i₁) : ℝ) : ℂ) * h n‖ =
        ((n : ℝ) + 1) ^ (1 - ρ i₁) * ‖h n‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)]
    rw [hL, hfac, hR, mul_pow, ← hsq, mul_comm]
    gcongr
  have hsum' := Summable.of_norm_bounded_eventually_nat hsum hbound
  have hinv : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ :=
    (summable_mul_left_iff (pow_ne_zero 2 (by positivity : ‖c i₁‖ / 2 ≠ 0))).mp hsum'
  refine Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp ?_)
  refine hinv.congr fun n => ?_
  push_cast
  rfl

/-- The coordinates of a finite combination `∑ c_j f^(r_j)` of the defect vectors. -/
theorem sum_smul_powerVec_apply {ι : Type*} (t : Finset ι) (ρ : ι → ℝ)
    (hρ : ∀ i, 1 / 2 < ρ i) (c : ι → ℂ) (n : ℕ) :
    (∑ i ∈ t, c i • powerVec (ρ i) (hρ i)) n =
      ∑ i ∈ t, c i * ((((n : ℝ) + 1) ^ (-ρ i) : ℝ) : ℂ) := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  rfl

/-- `ihs:hh:lem:continuum`: for `r ∈ (1/2, 3/2]`, the classes of the vectors
`f^(r) = (n^(-r))_{n ≥ 1}` in `H / Ran D` are linearly independent over `ℂ`. -/
theorem linearIndependent_powerVec_mkQ :
    LinearIndependent ℂ fun r : Set.Ioc (1 / 2 : ℝ) (3 / 2) =>
      (LinearMap.range invDiag.toLinearMap).mkQ (powerVec r.1 r.2.1) := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum i hi
  by_contra hgi
  have hmem :
      (∑ j ∈ t, g j • powerVec j.1 j.2.1) ∈ LinearMap.range invDiag.toLinearMap := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    simpa only [map_smul] using hsum
  rw [mem_range_invDiag_iff, memℓp_two_iff_summable_sq] at hmem
  refine not_summable_norm_mul_sum_sq t (fun j => j.1) Subtype.val_injective.injOn
    (fun j _ => j.2.2) g ⟨i, hi, hgi⟩ (hmem.congr fun n => ?_)
  rw [sum_smul_powerVec_apply t (fun j => j.1) (fun j => j.2.1) g n]

/-- In particular the vectors `f^(r)`, `r ∈ (1/2, 3/2]`, are linearly independent in `H`. -/
theorem linearIndependent_powerVec :
    LinearIndependent ℂ fun r : Set.Ioc (1 / 2 : ℝ) (3 / 2) => powerVec r.1 r.2.1 :=
  LinearIndependent.of_comp (LinearMap.range invDiag.toLinearMap).mkQ
    linearIndependent_powerVec_mkQ

/-- Each `f^(r)` with `r ∈ (1/2, 3/2]` lies outside `Ran D`. -/
theorem powerVec_notMem_range_invDiag {r : ℝ} (hr : 1 / 2 < r) (hr' : r ≤ 3 / 2) :
    powerVec r hr ∉ LinearMap.range invDiag.toLinearMap := by
  intro h
  have hne := linearIndependent_powerVec_mkQ.ne_zero ⟨r, hr, hr'⟩
  exact hne ((Submodule.Quotient.mk_eq_zero _).mpr h)

/-- `ihs:hh:sec:largecoker`: the vector `(n⁻¹)_{n ≥ 1} ∈ ℓ²` has no preimage under `D`. -/
theorem powerVec_one_notMem_range_invDiag :
    powerVec 1 (by norm_num) ∉ LinearMap.range invDiag.toLinearMap :=
  powerVec_notMem_range_invDiag _ (by norm_num)

/-- `ihs:hh:sec:largecoker`: `D` is not onto. -/
theorem not_surjective_invDiag : ¬ Function.Surjective invDiag := by
  intro h
  obtain ⟨y, hy⟩ := h (powerVec 1 (by norm_num))
  exact powerVec_one_notMem_range_invDiag (LinearMap.mem_range.mpr ⟨y, hy⟩)

/-- `ihs:hh:lem:continuum`, cardinality form: there are continuum many choices of `r`, so
`dim_ℂ (H / Ran D) ≥ 2^ℵ₀`. -/
theorem continuum_le_rank_quotient_range_invDiag :
    Cardinal.continuum ≤ Module.rank ℂ (ℓ²(ℕ, ℂ) ⧸ LinearMap.range invDiag.toLinearMap) := by
  have h := linearIndependent_powerVec_mkQ.cardinal_le_rank
  rwa [Cardinal.mk_Ioc_real (by norm_num)] at h

/-- The `D²` step of the proof of `ihs:hh:thm:continuum`: since `Ran D² ⊆ Ran D`, the classes of
the `f^(r)`, `r ∈ (1/2, 3/2]`, remain linearly independent modulo `Ran D²`. -/
theorem linearIndependent_powerVec_mkQ_sq :
    LinearIndependent ℂ fun r : Set.Ioc (1 / 2 : ℝ) (3 / 2) =>
      (LinearMap.range (invDiag * invDiag).toLinearMap).mkQ (powerVec r.1 r.2.1) := by
  have hle :
      LinearMap.range (invDiag * invDiag).toLinearMap ≤ LinearMap.range invDiag.toLinearMap := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨invDiag y, rfl⟩
  exact LinearIndependent.of_comp (Submodule.factor hle) linearIndependent_powerVec_mkQ

/-- `dim_ℂ (H / Ran D²) ≥ 2^ℵ₀`. -/
theorem continuum_le_rank_quotient_range_invDiag_sq :
    Cardinal.continuum ≤
      Module.rank ℂ (ℓ²(ℕ, ℂ) ⧸ LinearMap.range (invDiag * invDiag).toLinearMap) := by
  have h := linearIndependent_powerVec_mkQ_sq.cardinal_le_rank
  rwa [Cardinal.mk_Ioc_real (by norm_num)] at h

end PowerVectors

end

end Surreal.ContinuumDefects
