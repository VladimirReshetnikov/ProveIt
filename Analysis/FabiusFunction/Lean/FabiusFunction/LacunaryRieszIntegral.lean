import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exact integrals of lacunary Riesz products

The mean-value theory of the Fabius/Rvachev sinc product rests on one
exact orthogonality principle: a trigonometric product whose
frequencies grow fast enough cannot resonate down to a low frequency,
so its integral over a period sees only the constant term.  This file
proves that principle in a reusable, fully general form and derives the
exact `L²` identity used by the decay audit
(`docs/non-formalized-research-frontiers/drafts/rvachev_up_fourier_decay/
Rvachev_Up_Fourier_Decay_Comparative_Audit/`, Proposition "exact `L²`
identity").

* `integral_cos_int_freq` — the **frequency detector**:
  `∫ t in 0..1, cos (2π·K·t + ψ) = if K = 0 then cos ψ else 0`
  for every integer frequency `K` and phase `ψ`.
* `integral_cos_mul_rieszProduct_of_sum_lt` — the **master
  orthogonality theorem**, stated under the hypothesis its peeling
  induction actually consumes (sufficient for the conclusion, not
  necessary for it): the probe frequency `K` must be **dissociated**
  from the frequency block, `|K| + ∑_{i<j} m i < m j` for every `j`,
  so that no *nontrivial* signed combination `∑_j ε j · m j`
  (`ε j ∈ {-1, 0, 1}`) can reach `-K`.
  For arbitrary real amplitudes `a j` and phases `φ j`,
  `∫ t in 0..1, cos (2π·K·t + ψ) · ∏_{j<n} (1 + a j·cos (2π·m j·t + φ j))
     = if K = 0 then cos ψ else 0`.
  The classical Riesz-product mean value is the case `K = 0`, but the
  full statement identifies the Fourier coefficient of the product at
  every dissociated probe.  Dissociation is strictly stronger than
  lying below the spectral floor `m 0`: see **Sharpness** below.
* `integral_cos_mul_rieszProduct_of_add_sum_le` — the same conclusion
  under the `K`-free hypothesis **super-increasing with headroom
  `m 0`**, `∀ j, m 0 + ∑_{i<j} m i ≤ m j`, together with `|K| < m 0`:
  that much headroom makes every probe below the spectral floor
  dissociated.
* `integral_cos_mul_rieszProduct` — the classical Hadamard-gap form
  (`2·m j ≤ m (j+1)`), now a corollary through
  `add_sum_le_of_two_mul_le`.
* `integral_rieszProduct_of_superIncreasing` — the mean value: the
  product integrates to `1`.  The probe frequency is `K = 0` there, so
  plain super-increasingness `∀ j, ∑_{i<j} m i < m j` already
  suffices; `integral_rieszProduct` is the gap-`2` corollary (with
  `m 0 > 0`) via `superIncreasing_of_two_mul_le`.
* `integral_prod_sin_sq_of_superIncreasing` — the **exact sine-square
  identity** `∫ t in 0..1, ∏_{j<n} sin (π·m j·t)² = (1/2)ⁿ`, again for
  plain super-increasing frequencies; `integral_prod_sin_sq` is the
  gap-`2` corollary (with `m 0 > 0`), specialized by
  `integral_prod_sin_sq_pow` to geometric frequencies `bʲ` (`b ≥ 2`)
  and by `integral_prod_sin_sq_two_pow` to the dyadic case, which is
  the identity `I₂(n) = 2⁻ⁿ` of the decay audit.

The theorem is strictly more general than the audit's statement: the
frequencies need not be powers of two, they need not even be Hadamard
lacunary (`1, 3, 5, 10, 20, 40, …` is admissible while `2·3 ≤ 5`
fails), the factors may carry arbitrary amplitudes and phases, and the
probe frequency `K` ranges over every frequency dissociated from the
block.  A finite frequency list `m 0, …, m (n-1)` obeying the
hypothesis only up to index `n - 1` can always be extended to a
globally admissible sequence (double onward), so the global hypothesis
loses no applicability.

**Sharpness.**  For `K ≠ 0` the offset `m 0` in the super-increasing
hypothesis cannot simply be deleted: dissociation is a genuinely
stronger demand than `|K| < m 0`.  The frequencies `3, 4, 8, 16, …`
are super-increasing in the plain sense (`∑_{i<j} m i < m j` for every
`j`), and the probe `K = 1` lies below the floor `m 0 = 3`, yet the
difference `m 1 - m 0 = 1` resonates with the probe:
`∫ t in 0..1, cos (2π t)·(1 + cos (6π t))·(1 + cos (8π t)) = 1/4 ≠ 0`.
So plain super-increasingness is enough for the `K = 0` corollaries
below, but not in general once `K ≠ 0`.  This counterexample is
formalized in `FabiusFunction.RieszSharpness`:
`Fabius.integral_cos_mul_sharpProduct` gives the value `1/4`, and
`Fabius.exists_superIncreasing_probe_integral_ne` packages it as the
refutation of the weakened hypothesis.
-/

set_option autoImplicit false

open Finset intervalIntegral Real

namespace Fabius

/-- Integral of a cosine with linear argument over `[0, 1]`. -/
theorem integral_cos_linear (c d : ℝ) (hc : c ≠ 0) :
    ∫ t in (0:ℝ)..1, Real.cos (c * t + d) =
      (Real.sin (c + d) - Real.sin d) / c := by
  have h := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    Real.cos hc d
  simp only [mul_zero, zero_add, mul_one, integral_cos, smul_eq_mul] at h
  rw [h, div_eq_inv_mul]

/-- **The frequency detector**: over one period, a cosine with integer
frequency `K` and arbitrary phase `ψ` integrates to `cos ψ` when
`K = 0` and to `0` otherwise. -/
theorem integral_cos_int_freq (K : ℤ) (ψ : ℝ) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * (K : ℝ) * t + ψ) =
      if K = 0 then Real.cos ψ else 0 := by
  rcases eq_or_ne K 0 with hK | hK
  · subst hK
    simp
  · rw [if_neg hK]
    have hc : 2 * π * (K : ℝ) ≠ 0 := by
      have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have hKR : (K : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hK
      positivity
    rw [integral_cos_linear _ _ hc]
    have hper : Real.sin (2 * π * (K : ℝ) + ψ) = Real.sin ψ := by
      have := Real.sin_add_int_mul_two_pi ψ K
      rw [← this]
      ring_nf
    rw [hper, sub_self, zero_div]

/-- Product-to-sum formula for two cosines. -/
theorem cos_mul_cos_eq (A B : ℝ) :
    Real.cos A * Real.cos B =
      (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]; ring

/-- The factors of a Riesz product are continuous. -/
theorem continuous_rieszFactor (a φ : ℝ) (c : ℝ) :
    Continuous fun t : ℝ => 1 + a * Real.cos (c * t + φ) := by
  fun_prop

/-- A finite Riesz product is continuous. -/
theorem continuous_rieszProduct (m : ℕ → ℕ) (a φ : ℕ → ℝ) (n : ℕ) :
    Continuous fun t : ℝ =>
      ∏ j ∈ range n, (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) := by
  refine continuous_finsetProd _ fun j _ => ?_
  fun_prop

/-- A Hadamard-gap sequence is **super-increasing with headroom `m 0`**:
each frequency dominates the sum of all lower frequencies *plus* the
spectral floor `m 0`.  Induction on `j`:
`m 0 + ∑_{i<j+1} m i = (m 0 + ∑_{i<j} m i) + m j ≤ 2·m j ≤ m (j+1)`. -/
theorem add_sum_le_of_two_mul_le (m : ℕ → ℕ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (j : ℕ) :
    m 0 + ∑ i ∈ range j, m i ≤ m j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h := hgap j
      rw [Finset.sum_range_succ]
      omega

/-- A Hadamard-gap sequence whose first term is positive is
**super-increasing**: `∑_{i<j} m i < m j` for every `j`. -/
theorem superIncreasing_of_two_mul_le (m : ℕ → ℕ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (hpos : 0 < m 0) (j : ℕ) :
    ∑ i ∈ range j, m i < m j := by
  have h := add_sum_le_of_two_mul_le m hgap j
  omega

/-- **Master orthogonality theorem for lacunary Riesz products.**

Let `m 0, m 1, …` be integer frequencies, let `a j` and `φ j` be
arbitrary real amplitudes and phases, and let `K` be an integer probe
frequency *dissociated* from the frequency block in the precise sense
that `|K| + ∑_{i<j} m i < m j` for every `j` — no *nontrivial* signed
combination `∑_j ε j · m j` with `ε j ∈ {-1, 0, 1}` can then equal
`-K`.  Then
`∫ t in 0..1, cos (2π K t + ψ) · ∏_{j<n} (1 + a j cos (2π (m j) t + φ j))`
equals `cos ψ` if `K = 0` and `0` otherwise.

This hypothesis is exactly what the peeling induction consumes: after
the lowest frequency `m 0` is peeled off, the two shifted probes
`K ± m 0` still satisfy it for the shifted sequence `j ↦ m (j + 1)`,
because `|K ± m 0| + ∑_{i<j} m (i + 1) ≤ |K| + ∑_{i<j+1} m i < m (j+1)`.

This is the reusable engine behind every exact mean computation for the
dyadic sine products of the Fabius development. -/
theorem integral_cos_mul_rieszProduct_of_sum_lt :
    ∀ (n : ℕ) (m : ℕ → ℕ) (a φ : ℕ → ℝ) (K : ℤ) (ψ : ℝ),
      (∀ j, K.natAbs + ∑ i ∈ range j, m i < m j) →
      ∫ t in (0:ℝ)..1, Real.cos (2 * π * (K : ℝ) * t + ψ) *
          ∏ j ∈ range n, (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) =
        if K = 0 then Real.cos ψ else 0 := by
  intro n
  induction n with
  | zero =>
      intro m a φ K ψ _
      simpa using integral_cos_int_freq K ψ
  | succ n ih =>
      intro m a φ K ψ hdis
      -- The probe stays below the spectral floor.
      have hK : K.natAbs < m 0 := by
        have h := hdis 0
        simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h
        exact h
      -- Peel the lowest frequency `m 0` and shift the rest.
      set m' : ℕ → ℕ := fun j => m (j + 1) with hm'
      set a' : ℕ → ℝ := fun j => a (j + 1) with ha'
      set φ' : ℕ → ℝ := fun j => φ (j + 1) with hφ'
      -- The shifted sequence dominates its own partial sums with an
      -- extra `m 0` of headroom — exactly what the two shifted probe
      -- frequencies `K ± m 0` consume.
      have hkey : ∀ j, K.natAbs + m 0 + ∑ i ∈ range j, m' i < m' j := by
        intro j
        have h := hdis (j + 1)
        rw [Finset.sum_range_succ'] at h
        simp only [hm']
        omega
      -- The three probe frequencies appearing after linearization.
      have hdis₁ : ∀ j, K.natAbs + ∑ i ∈ range j, m' i < m' j := by
        intro j
        have h := hkey j
        omega
      have hdisSub : ∀ j,
          (K - (m 0 : ℤ)).natAbs + ∑ i ∈ range j, m' i < m' j := by
        intro j
        have h := hkey j
        omega
      have hdisAdd : ∀ j,
          (K + (m 0 : ℤ)).natAbs + ∑ i ∈ range j, m' i < m' j := by
        intro j
        have h := hkey j
        omega
      have hKsub0 : K - (m 0 : ℤ) ≠ 0 := by omega
      have hKadd0 : K + (m 0 : ℤ) ≠ 0 := by omega
      -- Abbreviate the shifted product.
      set P : ℝ → ℝ := fun t =>
        ∏ j ∈ range n, (1 + a' j * Real.cos (2 * π * (m' j : ℝ) * t + φ' j))
        with hP
      have hPcont : Continuous P := continuous_rieszProduct m' a' φ' n
      -- Pointwise linearization of the peeled factor.
      have hpoint : ∀ t : ℝ,
          Real.cos (2 * π * (K : ℝ) * t + ψ) *
            ∏ j ∈ range (n + 1),
              (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) =
          Real.cos (2 * π * (K : ℝ) * t + ψ) * P t +
            (a 0 / 2) *
              (Real.cos (2 * π * ((K - (m 0 : ℤ)) : ℝ) * t + (ψ - φ 0)) * P t) +
            (a 0 / 2) *
              (Real.cos (2 * π * ((K + (m 0 : ℤ)) : ℝ) * t + (ψ + φ 0)) * P t) := by
        intro t
        rw [Finset.prod_range_succ' (fun j =>
          (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j))) n]
        have hsub : 2 * π * ((K - (m 0 : ℤ)) : ℝ) * t + (ψ - φ 0) =
            (2 * π * (K : ℝ) * t + ψ) - (2 * π * (m 0 : ℝ) * t + φ 0) := by
          push_cast; ring
        have hadd : 2 * π * ((K + (m 0 : ℤ)) : ℝ) * t + (ψ + φ 0) =
            (2 * π * (K : ℝ) * t + ψ) + (2 * π * (m 0 : ℝ) * t + φ 0) := by
          push_cast; ring
        rw [hsub, hadd]
        have hcc := cos_mul_cos_eq (2 * π * (K : ℝ) * t + ψ)
          (2 * π * (m 0 : ℝ) * t + φ 0)
        simp only [hP, hm', ha', hφ']
        linear_combination (a 0 *
          ∏ j ∈ range n,
            (1 + a (j + 1) *
              Real.cos (2 * π * ((m (j + 1) : ℕ) : ℝ) * t + φ (j + 1)))) * hcc
      rw [intervalIntegral.integral_congr (g := fun t =>
          Real.cos (2 * π * (K : ℝ) * t + ψ) * P t +
            (a 0 / 2) *
              (Real.cos (2 * π * ((K - (m 0 : ℤ)) : ℝ) * t + (ψ - φ 0)) * P t) +
            (a 0 / 2) *
              (Real.cos (2 * π * ((K + (m 0 : ℤ)) : ℝ) * t + (ψ + φ 0)) * P t))
        (fun t _ => hpoint t)]
      -- Integrate the three pieces separately.
      have hi₁ : IntervalIntegrable
          (fun t => Real.cos (2 * π * (K : ℝ) * t + ψ) * P t)
          MeasureTheory.volume 0 1 := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hi₂ : IntervalIntegrable (fun t =>
          (a 0 / 2) *
            (Real.cos (2 * π * ((K - (m 0 : ℤ)) : ℝ) * t + (ψ - φ 0)) * P t))
          MeasureTheory.volume 0 1 := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hi₃ : IntervalIntegrable (fun t =>
          (a 0 / 2) *
            (Real.cos (2 * π * ((K + (m 0 : ℤ)) : ℝ) * t + (ψ + φ 0)) * P t))
          MeasureTheory.volume 0 1 := by
        apply Continuous.intervalIntegrable
        fun_prop
      rw [intervalIntegral.integral_add (hi₁.add hi₂) hi₃,
        intervalIntegral.integral_add hi₁ hi₂,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have e₁ := ih m' a' φ' K ψ hdis₁
      have e₂ := ih m' a' φ' (K - (m 0 : ℤ)) (ψ - φ 0) hdisSub
      have e₃ := ih m' a' φ' (K + (m 0 : ℤ)) (ψ + φ 0) hdisAdd
      rw [if_neg hKsub0] at e₂
      rw [if_neg hKadd0] at e₃
      simp only [hP] at e₁ e₂ e₃ ⊢
      push_cast at e₁ e₂ e₃ ⊢
      rw [e₁, e₂, e₃]
      simp

/-- **Master orthogonality theorem, super-increasing-with-headroom
form.**

If every frequency dominates the sum of all lower frequencies *plus*
the spectral floor `m 0` — `∀ j, m 0 + ∑_{i<j} m i ≤ m j` — then every
probe frequency `K` with `|K| < m 0` is dissociated from the frequency
block, so the master theorem applies.  This hypothesis is strictly
weaker than the Hadamard gap `2·m j ≤ m (j+1)`: the sequence
`1, 3, 5, 10, 20, 40, …` satisfies it and is not Hadamard lacunary.
It is strictly *stronger* than the plain super-increasingness
`∀ j, ∑_{i<j} m i < m j` used by the `K = 0` corollaries below, which
is why the name records the headroom rather than reading
`_of_superIncreasing`.

The offset `m 0` cannot simply be deleted: plain super-increasingness
`∀ j, ∑_{i<j} m i < m j` together with `|K| < m 0` does not suffice
once `K ≠ 0`.  See `Fabius.exists_superIncreasing_probe_integral_ne`
in `FabiusFunction.RieszSharpness` for the formalized witness
`m = (3, 4, 8, 16, …)`, `K = 1`.  That is a single witness: it does
not show this hypothesis is the weakest `K`-free hypothesis yielding
the conclusion. -/
theorem integral_cos_mul_rieszProduct_of_add_sum_le (n : ℕ)
    (m : ℕ → ℕ) (a φ : ℕ → ℝ) (K : ℤ) (ψ : ℝ)
    (hsi : ∀ j, m 0 + ∑ i ∈ range j, m i ≤ m j) (hK : K.natAbs < m 0) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * (K : ℝ) * t + ψ) *
        ∏ j ∈ range n, (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) =
      if K = 0 then Real.cos ψ else 0 :=
  integral_cos_mul_rieszProduct_of_sum_lt n m a φ K ψ fun j => by
    have h := hsi j
    omega

/-- **Master orthogonality theorem, Hadamard-gap form.**

Let `m 0, m 1, …` be integer frequencies with the Hadamard gap
`2·m j ≤ m (j+1)`, let `a j` and `φ j` be arbitrary real amplitudes and
phases, and let `K` be an integer probe frequency with `|K| < m 0`.
Then
`∫ t in 0..1, cos (2π K t + ψ) · ∏_{j<n} (1 + a j cos (2π (m j) t + φ j))`
equals `cos ψ` if `K = 0` and `0` otherwise: no *nontrivial* signed
combination of gap-`2` frequencies can cancel a probe below the
spectral floor.

This is the historical statement; it is now the special case of
`integral_cos_mul_rieszProduct_of_add_sum_le` obtained from
`add_sum_le_of_two_mul_le`. -/
theorem integral_cos_mul_rieszProduct :
    ∀ (n : ℕ) (m : ℕ → ℕ) (a φ : ℕ → ℝ) (K : ℤ) (ψ : ℝ),
      (∀ j, 2 * m j ≤ m (j + 1)) → K.natAbs < m 0 →
      ∫ t in (0:ℝ)..1, Real.cos (2 * π * (K : ℝ) * t + ψ) *
          ∏ j ∈ range n, (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) =
        if K = 0 then Real.cos ψ else 0 := by
  intro n m a φ K ψ hgap hK
  exact integral_cos_mul_rieszProduct_of_add_sum_le n m a φ K ψ
    (add_sum_le_of_two_mul_le m hgap) hK

/-- **Riesz-product mean value, super-increasing form**: over one
period, a lacunary Riesz product whose integer frequencies satisfy
`∑_{i<j} m i < m j` integrates to `1`, for every choice of amplitudes
and phases.  Here the probe frequency is `K = 0`, so no headroom below
the spectral floor is needed and plain super-increasingness is
enough. -/
theorem integral_rieszProduct_of_superIncreasing (n : ℕ) (m : ℕ → ℕ)
    (a φ : ℕ → ℝ) (hsi : ∀ j, ∑ i ∈ range j, m i < m j) :
    ∫ t in (0:ℝ)..1,
        ∏ j ∈ range n, (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) = 1 := by
  have h := integral_cos_mul_rieszProduct_of_sum_lt n m a φ 0 0
    (fun j => by
      have hj := hsi j
      omega)
  simpa using h

/-- **Riesz-product mean value**: over one period, a lacunary Riesz
product with gap-`2` integer frequencies and `m 0 > 0` integrates to
`1`, for every choice of amplitudes and phases.  The positivity of
`m 0` is not a convention: for `m ≡ 0` the gap holds and the product
integrates to `2ⁿ` when `a ≡ 1`, `φ ≡ 0`. -/
theorem integral_rieszProduct (n : ℕ) (m : ℕ → ℕ) (a φ : ℕ → ℝ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (hpos : 0 < m 0) :
    ∫ t in (0:ℝ)..1,
        ∏ j ∈ range n, (1 + a j * Real.cos (2 * π * (m j : ℝ) * t + φ j)) = 1 := by
  have h := integral_cos_mul_rieszProduct n m a φ 0 0 hgap (by simpa using hpos)
  simpa using h

/-- **Exact sine-square identity, super-increasing form**: for integer
frequencies with `∑_{i<j} m i < m j`,
`∫ t in 0..1, ∏_{j<n} sin (π (m j) t)² = (1/2)ⁿ` — exactly, for every
`n`. -/
theorem integral_prod_sin_sq_of_superIncreasing (n : ℕ) (m : ℕ → ℕ)
    (hsi : ∀ j, ∑ i ∈ range j, m i < m j) :
    ∫ t in (0:ℝ)..1,
        ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2 = (1 / 2 : ℝ) ^ n := by
  have hfac : ∀ (j : ℕ) (t : ℝ),
      Real.sin (π * (m j : ℝ) * t) ^ 2 =
        (1 / 2 : ℝ) * (1 + (-1) * Real.cos (2 * π * (m j : ℝ) * t + 0)) := by
    intro j t
    have h := Real.sin_sq_eq_half_sub (π * (m j : ℝ) * t)
    rw [h]
    ring_nf
  have hprod : ∀ t : ℝ,
      ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2 =
        (1 / 2 : ℝ) ^ n *
          ∏ j ∈ range n,
            (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0)) := by
    intro t
    calc ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2
        = ∏ j ∈ range n, ((1 / 2 : ℝ) *
            (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0))) :=
          Finset.prod_congr rfl fun j _ => hfac j t
      _ = (1 / 2 : ℝ) ^ n *
            ∏ j ∈ range n,
              (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [intervalIntegral.integral_congr (g := fun t =>
      (1 / 2 : ℝ) ^ n *
        ∏ j ∈ range n, (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0)))
    (fun t _ => hprod t)]
  rw [intervalIntegral.integral_const_mul,
    integral_rieszProduct_of_superIncreasing n m (fun _ => (-1 : ℝ))
      (fun _ => 0) hsi,
    mul_one]

/-- **Exact sine-square identity**: for gap-`2` integer frequencies
with `m 0 > 0`,
`∫ t in 0..1, ∏_{j<n} sin (π (m j) t)² = (1/2)ⁿ` — exactly, for every
`n`.  This is the reusable general form of the audit's identity
`I₂(n) = 2⁻ⁿ`.  Again `m 0 > 0` is essential: `m ≡ 0` satisfies the
gap and makes the integrand vanish identically for `n ≥ 1`. -/
theorem integral_prod_sin_sq (n : ℕ) (m : ℕ → ℕ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (hpos : 0 < m 0) :
    ∫ t in (0:ℝ)..1,
        ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2 = (1 / 2 : ℝ) ^ n :=
  integral_prod_sin_sq_of_superIncreasing n m
    (superIncreasing_of_two_mul_le m hgap hpos)

/-- Geometric frequencies `bʲ` with any integer base `b ≥ 2` satisfy the
gap condition, so `∫ t in 0..1, ∏_{j<n} sin (π bʲ t)² = (1/2)ⁿ`. -/
theorem integral_prod_sin_sq_pow (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∫ t in (0:ℝ)..1,
        ∏ j ∈ range n, Real.sin (π * (b : ℝ) ^ j * t) ^ 2 = (1 / 2 : ℝ) ^ n := by
  have h := integral_prod_sin_sq n (fun j => b ^ j)
    (fun j => by
      have : 2 * b ^ j ≤ b * b ^ j := Nat.mul_le_mul_right _ hb
      simpa [pow_succ, mul_comm] using this)
    (by simp)
  have hcast : ∀ (j : ℕ) (t : ℝ),
      Real.sin (π * ((b ^ j : ℕ) : ℝ) * t) = Real.sin (π * (b : ℝ) ^ j * t) := by
    intro j t
    norm_num
  simpa [hcast] using h

/-- **The dyadic case** (`I₂(n) = 2⁻ⁿ` of the decay audit):
`∫ t in 0..1, ∏_{j<n} sin (π 2ʲ t)² = (1/2)ⁿ`.  This is the exact
root-mean-square input behind the `κ₂ = log₂(2π)` layer of the
Fourier-decay spectrum of the Rvachev up-function. -/
theorem integral_prod_sin_sq_two_pow (n : ℕ) :
    ∫ t in (0:ℝ)..1,
        ∏ j ∈ range n, Real.sin (π * 2 ^ j * t) ^ 2 = (1 / 2 : ℝ) ^ n := by
  have h := integral_prod_sin_sq_pow 2 le_rfl n
  have hcast : ∀ (j : ℕ) (t : ℝ),
      Real.sin (π * ((2 : ℕ) : ℝ) ^ j * t) = Real.sin (π * (2 : ℝ) ^ j * t) := by
    intro j t
    norm_num
  simpa [hcast] using h

end Fabius
