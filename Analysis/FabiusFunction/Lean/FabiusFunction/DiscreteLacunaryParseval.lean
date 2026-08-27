import FabiusFunction.LacunaryRieszIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Field.GeomSum

/-!
# Discrete orthogonality of lacunary Riesz products

The dyadic grid `{q/2ⁿ : q < 2ⁿ}` resolves the Thue–Morse sine product
exactly: sampling commutes with the mean.  This file proves the
discrete counterpart of `LacunaryRieszIntegral` — the same peeling
induction, with the period integral replaced by a full-period sum over
an `N`-point grid — and derives the discrete Parseval identity
`∑_{q<2ⁿ} ∏_{j<n} sin(π 2ʲ q/2ⁿ)² = 1` of the Fourier-decay audit
(the sampled `L²` normalization of the Thue–Morse polynomial).

* `sum_exp_int_freq` — the **discrete frequency detector**, complex
  form: `∑_{q<N} exp(2πi K q/N) = N` if `N ∣ K` and `0` otherwise —
  for every integer `K`, by the geometric sum.
* `sum_cos_int_freq` — the real form with an arbitrary phase:
  `∑_{q<N} cos(2π K q/N + ψ) = N cos ψ` if `N ∣ K`, else `0`.
* `sum_cos_mul_rieszProduct` — the **master discrete orthogonality
  theorem**: for integer frequencies with the Hadamard gap
  `2·m j ≤ m (j+1)`, arbitrary amplitudes and phases, any probe
  `|K| < m 0`, and any grid size `N ≥ m n`,
  `∑_{q<N} cos(2π K q/N + ψ)·∏_{j<n}(1 + a j cos(2π m j q/N + φ j))`
  equals `N cos ψ` if `K = 0` and `0` otherwise.  The grid hypothesis
  `m n ≤ N` is exactly what keeps every resonance frequency reachable
  by the product strictly inside `(-N, N)`.
* `sum_rieszProduct` — sampled Riesz products have mean exactly `1` on
  any admissible grid.
* `sum_prod_sin_sq` / `sum_prod_sin_sq_two_pow` — the sampled sine
  identity `∑_{q<N} ∏_{j<n} sin(π m j q/N)² = N/2ⁿ` and its dyadic
  case `N = 2ⁿ`, `m j = 2ʲ`, where the grid bound holds with equality:
  `∑_{q<2ⁿ} ∏_{j<n} sin(π 2ʲ q/2ⁿ)² = 1`.

Everything is stated for general gap-`2` frequency sequences and
general grids, strictly more general than the audit's dyadic case.
-/

set_option autoImplicit false

open Finset Real

namespace Fabius

/-- **Discrete frequency detector, complex form**: over the `N`-point
grid, `∑_{q<N} exp(2πi K q/N)` is `N` when `N ∣ K` and `0` otherwise. -/
theorem sum_exp_int_freq (N : ℕ) (hN : 0 < N) (K : ℤ) :
    ∑ q ∈ range N, Complex.exp (2 * π * Complex.I * K * q / N) =
      if (N : ℤ) ∣ K then (N : ℂ) else 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rcases em ((N : ℤ) ∣ K) with hdvd | hdvd
  · obtain ⟨c, hc⟩ := hdvd
    rw [if_pos ⟨c, hc⟩]
    have hterm : ∀ q ∈ range N,
        Complex.exp (2 * π * Complex.I * K * q / N) = 1 := by
      intro q _
      have harg : 2 * π * Complex.I * (K : ℂ) * q / N =
          ((c * q : ℤ) : ℂ) * (2 * π * Complex.I) := by
        have hKC : (K : ℂ) = (N : ℂ) * (c : ℂ) := by
          rw [hc]
          push_cast
          ring
        rw [hKC]
        push_cast
        field_simp
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
    simp
  · rw [if_neg hdvd]
    set w : ℂ := 2 * π * Complex.I * K / N with hw
    have hterm : ∀ q ∈ range N,
        Complex.exp (2 * π * Complex.I * K * q / N) = Complex.exp w ^ q := by
      intro q _
      rw [← Complex.exp_nat_mul]
      congr 1
      rw [hw]
      field_simp
    have hζN : Complex.exp w ^ N = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (N : ℂ) * w = (K : ℂ) * (2 * π * Complex.I) := by
        rw [hw]
        field_simp
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    have hζ1 : Complex.exp w ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      rw [hw, div_eq_iff hNC] at hk
      have h5 : (2 * (π : ℂ) * Complex.I) * (K : ℂ) =
          (2 * (π : ℂ) * Complex.I) * ((k : ℂ) * N) := by
        linear_combination hk
      have h6 : (K : ℂ) = (k : ℂ) * N :=
        mul_left_cancel₀ Complex.two_pi_I_ne_zero h5
      have h7 : K = k * N := by exact_mod_cast h6
      exact hdvd ⟨k, by rw [h7]; ring⟩
    rw [Finset.sum_congr rfl hterm, geom_sum_eq hζ1, hζN, sub_self, zero_div]

/-- **Discrete frequency detector, real form**: for every integer `K`
and phase `ψ`, `∑_{q<N} cos(2π K q/N + ψ)` is `N·cos ψ` when `N ∣ K`
and `0` otherwise. -/
theorem sum_cos_int_freq (N : ℕ) (hN : 0 < N) (K : ℤ) (ψ : ℝ) :
    ∑ q ∈ range N, Real.cos (2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ) =
      if (N : ℤ) ∣ K then (N : ℝ) * Real.cos ψ else 0 := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hexp_re : (Complex.exp ((ψ : ℂ) * Complex.I)).re = Real.cos ψ := by
    rw [Complex.exp_mul_I, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    ring
  have hexp_im : (Complex.exp ((ψ : ℂ) * Complex.I)).im = Real.sin ψ := by
    rw [Complex.exp_mul_I, Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    ring
  have hre : ∀ q : ℕ,
      Real.cos (2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ) =
        (Complex.exp ((ψ : ℂ) * Complex.I) *
          Complex.exp (2 * π * Complex.I * K * q / N)).re := by
    intro q
    rw [← Complex.exp_add]
    have harg : (ψ : ℂ) * Complex.I + 2 * π * Complex.I * K * q / N =
        ((2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp
      ring
    rw [harg, Complex.exp_mul_I, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_im]
    ring
  calc ∑ q ∈ range N, Real.cos (2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ)
      = (∑ q ∈ range N, Complex.exp ((ψ : ℂ) * Complex.I) *
          Complex.exp (2 * π * Complex.I * K * q / N)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun q _ => hre q
    _ = (Complex.exp ((ψ : ℂ) * Complex.I) *
          ∑ q ∈ range N, Complex.exp (2 * π * Complex.I * K * q / N)).re := by
        rw [Finset.mul_sum]
    _ = if (N : ℤ) ∣ K then (N : ℝ) * Real.cos ψ else 0 := by
        rw [sum_exp_int_freq N hN K]
        rcases em ((N : ℤ) ∣ K) with h | h
        · rw [if_pos h, if_pos h]
          rw [Complex.mul_re, hexp_re, hexp_im]
          simp [mul_comm]
        · rw [if_neg h, if_neg h, mul_zero, Complex.zero_re]

/-- **Master discrete orthogonality theorem for lacunary Riesz
products.**  Sampling on any grid of size `N ≥ m n` is exact: for
Hadamard-gapped integer frequencies, arbitrary amplitudes and phases,
and any probe `|K| < m 0`,
`∑_{q<N} cos(2π K q/N + ψ)·∏_{j<n}(1 + a j·cos(2π m j q/N + φ j))`
equals `N·cos ψ` for `K = 0` and vanishes otherwise. -/
theorem sum_cos_mul_rieszProduct :
    ∀ (n : ℕ) (m : ℕ → ℕ) (a φ : ℕ → ℝ) (K : ℤ) (ψ : ℝ) (N : ℕ),
      (∀ j, 2 * m j ≤ m (j + 1)) → K.natAbs < m 0 → m n ≤ N → 0 < N →
      ∑ q ∈ range N, (Real.cos (2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ) *
          ∏ j ∈ range n,
            (1 + a j * Real.cos (2 * π * (m j : ℝ) * ((q : ℝ) / N) + φ j))) =
        if K = 0 then (N : ℝ) * Real.cos ψ else 0 := by
  intro n
  induction n with
  | zero =>
      intro m a φ K ψ N hgap hK hmN hN0
      simp only [range_zero, prod_empty, mul_one]
      rw [sum_cos_int_freq N hN0 K ψ]
      rcases eq_or_ne K 0 with hK0 | hK0
      · subst hK0
        rw [if_pos (dvd_zero _), if_pos rfl]
      · rw [if_neg hK0]
        have hndvd : ¬ (N : ℤ) ∣ K := by
          intro hdvd
          have h1 : N ∣ K.natAbs := by
            have := Int.natAbs_dvd_natAbs.mpr hdvd
            simpa using this
          have h2 : K.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hK0
          have h3 : N ≤ K.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
          omega
        rw [if_neg hndvd]
  | succ n ih =>
      intro m a φ K ψ N hgap hK hmN hN0
      set m' : ℕ → ℕ := fun j => m (j + 1) with hm'
      set a' : ℕ → ℝ := fun j => a (j + 1) with ha'
      set φ' : ℕ → ℝ := fun j => φ (j + 1) with hφ'
      have hgap' : ∀ j, 2 * m' j ≤ m' (j + 1) := fun j => hgap (j + 1)
      have hgap0 : 2 * m 0 ≤ m (0 + 1) := hgap 0
      have hmN' : m' n ≤ N := hmN
      have hK₁ : K.natAbs < m' 0 := by
        simp only [hm']
        omega
      have hKsub : (K - (m 0 : ℤ)).natAbs < m' 0 := by
        simp only [hm']
        omega
      have hKadd : (K + (m 0 : ℤ)).natAbs < m' 0 := by
        simp only [hm']
        omega
      have hKsub0 : K - (m 0 : ℤ) ≠ 0 := by omega
      have hKadd0 : K + (m 0 : ℤ) ≠ 0 := by omega
      set P : ℝ → ℝ := fun t =>
        ∏ j ∈ range n, (1 + a' j * Real.cos (2 * π * (m' j : ℝ) * t + φ' j))
        with hP
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
      have hsum : ∑ q ∈ range N,
          (Real.cos (2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ) *
            ∏ j ∈ range (n + 1),
              (1 + a j * Real.cos (2 * π * (m j : ℝ) * ((q : ℝ) / N) + φ j))) =
          ∑ q ∈ range N,
            (Real.cos (2 * π * (K : ℝ) * ((q : ℝ) / N) + ψ) * P ((q : ℝ) / N) +
              (a 0 / 2) *
                (Real.cos (2 * π * ((K - (m 0 : ℤ)) : ℝ) * ((q : ℝ) / N) +
                  (ψ - φ 0)) * P ((q : ℝ) / N)) +
              (a 0 / 2) *
                (Real.cos (2 * π * ((K + (m 0 : ℤ)) : ℝ) * ((q : ℝ) / N) +
                  (ψ + φ 0)) * P ((q : ℝ) / N))) :=
        Finset.sum_congr rfl fun q _ => hpoint ((q : ℝ) / N)
      rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      have e₁ := ih m' a' φ' K ψ N hgap' hK₁ hmN' hN0
      have e₂ := ih m' a' φ' (K - (m 0 : ℤ)) (ψ - φ 0) N hgap' hKsub hmN' hN0
      have e₃ := ih m' a' φ' (K + (m 0 : ℤ)) (ψ + φ 0) N hgap' hKadd hmN' hN0
      rw [if_neg hKsub0] at e₂
      rw [if_neg hKadd0] at e₃
      simp only [hP] at e₁ e₂ e₃ ⊢
      push_cast at e₁ e₂ e₃ ⊢
      rw [e₁, e₂, e₃]
      simp

/-- **Sampled Riesz-product mean value**: on any grid of size
`N ≥ m n`, a lacunary Riesz product with gap-`2` integer frequencies
sums to exactly `N`. -/
theorem sum_rieszProduct (n : ℕ) (m : ℕ → ℕ) (a φ : ℕ → ℝ) (N : ℕ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (hpos : 0 < m 0) (hmN : m n ≤ N)
    (hN0 : 0 < N) :
    ∑ q ∈ range N,
        ∏ j ∈ range n,
          (1 + a j * Real.cos (2 * π * (m j : ℝ) * ((q : ℝ) / N) + φ j)) =
      (N : ℝ) := by
  have h := sum_cos_mul_rieszProduct n m a φ 0 0 N hgap
    (by simpa using hpos) hmN hN0
  simpa using h

/-- **Sampled sine-square identity**: for gap-`2` integer frequencies
and any grid of size `N ≥ m n`,
`∑_{q<N} ∏_{j<n} sin (π (m j) q/N)² = N/2ⁿ`. -/
theorem sum_prod_sin_sq (n : ℕ) (m : ℕ → ℕ) (N : ℕ)
    (hgap : ∀ j, 2 * m j ≤ m (j + 1)) (hpos : 0 < m 0) (hmN : m n ≤ N)
    (hN0 : 0 < N) :
    ∑ q ∈ range N,
        ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * ((q : ℝ) / N)) ^ 2 =
      (N : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hprod : ∀ t : ℝ,
      ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2 =
        (1 / 2 : ℝ) ^ n *
          ∏ j ∈ range n,
            (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0)) := by
    intro t
    have hfac : ∀ j : ℕ,
        Real.sin (π * (m j : ℝ) * t) ^ 2 =
          (1 / 2 : ℝ) * (1 + (-1) * Real.cos (2 * π * (m j : ℝ) * t + 0)) := by
      intro j
      have h := Real.sin_sq_eq_half_sub (π * (m j : ℝ) * t)
      rw [h]
      ring_nf
    calc ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * t) ^ 2
        = ∏ j ∈ range n, ((1 / 2 : ℝ) *
            (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0))) :=
          Finset.prod_congr rfl fun j _ => hfac j
      _ = (1 / 2 : ℝ) ^ n *
            ∏ j ∈ range n,
              (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * t + 0)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hsum : ∑ q ∈ range N,
      ∏ j ∈ range n, Real.sin (π * (m j : ℝ) * ((q : ℝ) / N)) ^ 2 =
      ∑ q ∈ range N, ((1 / 2 : ℝ) ^ n *
        ∏ j ∈ range n,
          (1 + (-1 : ℝ) * Real.cos (2 * π * (m j : ℝ) * ((q : ℝ) / N) + 0))) :=
    Finset.sum_congr rfl fun q _ => hprod ((q : ℝ) / N)
  rw [hsum, ← Finset.mul_sum,
    sum_rieszProduct n m (fun _ => (-1 : ℝ)) (fun _ => 0) N hgap hpos hmN hN0]
  ring

/-- **The discrete Parseval identity of the decay audit**: on the dyadic
grid of its own scale, the Thue–Morse sine product satisfies
`∑_{q<2ⁿ} ∏_{j<n} sin (π 2ʲ q/2ⁿ)² = 1` — exactly, for every `n`.
The grid bound `m n ≤ N` holds here with equality (`2ⁿ = 2ⁿ`): the
sampled Parseval sits at the edge of the admissible resolution. -/
theorem sum_prod_sin_sq_two_pow (n : ℕ) :
    ∑ q ∈ range (2 ^ n),
        ∏ j ∈ range n, Real.sin (π * 2 ^ j * ((q : ℝ) / 2 ^ n)) ^ 2 = 1 := by
  have h := sum_prod_sin_sq n (fun j => 2 ^ j) (2 ^ n)
    (fun j => by
      have h2 : 2 * 2 ^ j ≤ 2 ^ (j + 1) := by
        rw [pow_succ, Nat.mul_comm]
      exact h2)
    (by simp) le_rfl (Nat.two_pow_pos n)
  have hcast : ∀ (j q : ℕ),
      Real.sin (π * ((2 ^ j : ℕ) : ℝ) * ((q : ℝ) / ((2 ^ n : ℕ) : ℝ))) =
        Real.sin (π * (2 : ℝ) ^ j * ((q : ℝ) / (2 : ℝ) ^ n)) := by
    intro j q
    norm_num
  calc ∑ q ∈ range (2 ^ n),
        ∏ j ∈ range n, Real.sin (π * 2 ^ j * ((q : ℝ) / 2 ^ n)) ^ 2
      = ∑ q ∈ range (2 ^ n),
        ∏ j ∈ range n,
          Real.sin (π * ((2 ^ j : ℕ) : ℝ) * ((q : ℝ) / ((2 ^ n : ℕ) : ℝ))) ^ 2 := by
        refine Finset.sum_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
        rw [hcast]
    _ = ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n := h
    _ = 1 := by
        push_cast
        rw [div_pow, one_pow]
        field_simp
