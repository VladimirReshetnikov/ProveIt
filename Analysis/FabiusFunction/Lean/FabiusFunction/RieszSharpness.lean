import FabiusFunction.LacunaryRieszIntegral

/-!
# The headroom offset in the lacunary Riesz theorem is not removable

`LacunaryRieszIntegral` proves
`Fabius.integral_cos_mul_rieszProduct_of_add_sum_le`: if the integer
frequencies are **super-increasing with headroom `m 0`**,
`∀ j, m 0 + ∑_{i<j} m i ≤ m j`, and the probe frequency satisfies
`|K| < m 0`, then

`∫ t in 0..1, cos (2π K t + ψ) ·
  ∏_{j<n} (1 + a j · cos (2π (m j) t + φ j))`

equals `cos ψ` when `K = 0` and `0` otherwise.  The "Sharpness"
paragraph of its module docstring records, *in prose only*, a hand
computation showing that the offset `m 0` cannot simply be deleted
from the hypothesis: plain super-increasingness
`∀ j, ∑_{i<j} m i < m j` together with `|K| < m 0` does not suffice
once `K ≠ 0`.  The theorem's own docstring names the witness and
points there.  This file turns that hand computation into theorems.

## The witness

The frequency sequence is `3, 4, 8, 16, 32, …` (`sharpFreq`), the
amplitudes are `a ≡ 1`, the phases `φ ≡ 0`, the probe is `K = 1` with
`ψ = 0`, and only the first two factors are used (`n = 2`).  Then:

* the sequence is *globally* super-increasing,
  `∀ j, ∑_{i<j} m i < m j` (`superIncreasing_sharpFreq`);
* the probe lies strictly below the spectral floor,
  `|K| = 1 < 3 = m 0` (`natAbs_one_lt_sharpFreq_zero`);
* the headroom hypothesis nevertheless fails, already at `j = 1`:
  `m 0 + ∑_{i<1} m i = 3 + 3 = 6` is not `≤ m 1 = 4`
  (`not_add_sum_le_sharpFreq_one`, `not_add_sum_le_sharpFreq`);
* and the integral is `1/4`, not `0`
  (`integral_cos_mul_sharpProduct`,
  `integral_cos_mul_sharpProduct_ne_zero`):
  `∫ t in 0..1, cos (2π t) · (1 + cos (6π t)) · (1 + cos (8π t)) = 1/4`.

The resonance is visible in the expansion
(`cos_riesz_three_four`, `cos_mul_sharpProduct_eq`): the integrand is
a constant `1/4` plus seven cosines of nonzero integer frequency, so
only the constant survives integration, and it comes from the
`cos²(2π t)` produced by
`cos(2π t) · cos(6π t) · cos(8π t)`, i.e. from the difference
`m 1 - m 0 = 1` meeting the probe `K = 1`.

`exists_superIncreasing_probe_integral_ne` packages this as the
refutation: there exist `n`, `m`, `a`, `φ`, `K`, `ψ` with `m`
super-increasing, `|K| < m 0` and `K ≠ 0` for which the integral
differs from `if K = 0 then cos ψ else 0`.

## What this does and does not establish

This refutes the weakening of
`integral_cos_mul_rieszProduct_of_add_sum_le` obtained by replacing
`∀ j, m 0 + ∑_{i<j} m i ≤ m j` with `∀ j, ∑_{i<j} m i < m j`, keeping
`|K| < m 0`.  Nothing here shows that the headroom hypothesis is
necessary in any stronger or more general sense: it is a single
witness, and no claim is made that the headroom hypothesis is the
weakest `K`-free hypothesis implying the conclusion, nor that it is
necessary for any *particular* frequency sequence.  The dissociation
hypothesis of `integral_cos_mul_rieszProduct_of_sum_lt` is untouched:
this file neither refutes it nor shows it necessary.

## Main declarations

* `sharpFreq` — the witness frequency sequence `3, 4, 8, 16, 32, …`.
* `sharpFreq_zero`, `sharpFreq_succ`, `sharpFreq_one` — its values.
* `sum_range_sharpFreq_succ` — `(∑_{i<j+1} m i) + 1 = 2^(j+2)`.
* `superIncreasing_sharpFreq` — global super-increasingness.
* `not_add_sum_le_sharpFreq_one` — headroom fails at `j = 1`.
* `not_add_sum_le_sharpFreq` — hence it fails globally.
* `natAbs_one_lt_sharpFreq_zero` — the probe is below the floor.
* `integral_cos_two_pi_int` — `∫₀¹ cos (2π k t) = 0` for `k ≠ 0`.
* `integral_cos_two_pi_of_eq` — the same with the frequency supplied
  as a real number equal to an integer.
* `integral_add_harmonic_eq` — peeling one harmonic off an integral
  over the period leaves the integral unchanged.
* `cos_riesz_three_four` — the product-to-sum expansion of
  `cos u (1 + cos 3u)(1 + cos 4u)` into `1/4` plus seven cosines.
* `cos_mul_sharpProduct_eq` — the same expansion in the exact shape of
  the master theorem's integrand.
* `integral_sharp_expansion` — the expansion integrates to `1/4`.
* `integral_cos_mul_sharpProduct` — the witness integral is `1/4`.
* `integral_cos_mul_sharpProduct_ne_zero` — hence it is not `0`.
* `exists_superIncreasing_probe_integral_ne` — the capstone
  refutation.
-/

set_option autoImplicit false

open Finset intervalIntegral Real

namespace Fabius

/-! ### The witness frequency sequence -/

/-- The witness frequency sequence `3, 4, 8, 16, 32, …`: the value at
`0` is `3` and the value at `j + 1` is `2 ^ (j + 2)`.  It is
super-increasing (`superIncreasing_sharpFreq`) but does not have the
headroom `m 0` demanded by
`integral_cos_mul_rieszProduct_of_add_sum_le`
(`not_add_sum_le_sharpFreq`). -/
def sharpFreq : ℕ → ℕ
  | 0 => 3
  | j + 1 => 2 ^ (j + 2)

/-- The spectral floor of the witness sequence is `3`. -/
theorem sharpFreq_zero : sharpFreq 0 = 3 := rfl

/-- Past the first index the witness sequence doubles: `m (j+1) =
2 ^ (j + 2)`. -/
theorem sharpFreq_succ (j : ℕ) : sharpFreq (j + 1) = 2 ^ (j + 2) :=
  rfl

/-- The second frequency of the witness sequence is `4`. -/
theorem sharpFreq_one : sharpFreq 1 = 4 := by
  have h := sharpFreq_succ 0
  norm_num at h
  exact h

/-- The partial sums of the witness sequence are one less than the
next power of two: `∑_{i<j+1} m i + 1 = 2 ^ (j + 2)`.  (For `j = 0`
this reads `3 + 1 = 4`.) -/
theorem sum_range_sharpFreq_succ (j : ℕ) :
    (∑ i ∈ range (j + 1), sharpFreq i) + 1 = 2 ^ (j + 2) := by
  induction j with
  | zero => norm_num [Finset.sum_range_one, sharpFreq_zero]
  | succ j ih =>
      have hp : (2 : ℕ) ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
      rw [Finset.sum_range_succ, sharpFreq_succ, hp]
      omega

/-- The witness sequence is **super-increasing** in the plain sense
`∀ j, ∑_{i<j} m i < m j`, for *every* index `j`: at `j = 0` this is
`0 < 3`, and at `j + 1` it is `2 ^ (j + 2) - 1 < 2 ^ (j + 2)`. -/
theorem superIncreasing_sharpFreq (j : ℕ) :
    ∑ i ∈ range j, sharpFreq i < sharpFreq j := by
  cases j with
  | zero =>
      rw [Finset.sum_range_zero, sharpFreq_zero]
      norm_num
  | succ k =>
      have h := sum_range_sharpFreq_succ k
      rw [sharpFreq_succ]
      omega

/-- The headroom hypothesis of
`integral_cos_mul_rieszProduct_of_add_sum_le` fails for the witness
sequence already at `j = 1`: `m 0 + ∑_{i<1} m i = 3 + 3 = 6` is not
`≤ m 1 = 4`. -/
theorem not_add_sum_le_sharpFreq_one :
    ¬ (sharpFreq 0 + ∑ i ∈ range 1, sharpFreq i ≤ sharpFreq 1) := by
  rw [Finset.sum_range_one, sharpFreq_zero, sharpFreq_one]
  omega

/-- Consequently the witness sequence does not satisfy the headroom
hypothesis `∀ j, m 0 + ∑_{i<j} m i ≤ m j` at all. -/
theorem not_add_sum_le_sharpFreq :
    ¬ (∀ j, sharpFreq 0 + ∑ i ∈ range j, sharpFreq i ≤ sharpFreq j) :=
  fun h => not_add_sum_le_sharpFreq_one (h 1)

/-- The probe frequency `K = 1` lies strictly below the spectral floor
`m 0 = 3` of the witness sequence. -/
theorem natAbs_one_lt_sharpFreq_zero :
    (1 : ℤ).natAbs < sharpFreq 0 := by
  rw [sharpFreq_zero, Int.natAbs_one]
  norm_num

/-! ### Integrating single harmonics over one period -/

/-- Phase-free form of the frequency detector: a cosine of nonzero
integer frequency has mean `0` over one period. -/
theorem integral_cos_two_pi_int (k : ℤ) (hk : k ≠ 0) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * (k : ℝ) * t) = 0 := by
  have h := integral_cos_int_freq k 0
  rw [if_neg hk] at h
  simp only [add_zero] at h
  exact h

/-- The previous statement with the frequency presented as a real
number `r` that happens to equal a nonzero integer `k`.  This shape is
what the numeral-valued harmonics below need. -/
theorem integral_cos_two_pi_of_eq (r : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hr : r = (k : ℝ)) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * r * t) = 0 := by
  subst hr
  exact integral_cos_two_pi_int k hk

/-- **Peeling one harmonic.**  Adding `w · cos (2π r t)` with `r` a
nonzero integer to any integrand does not change the integral over one
period.  No hypothesis on `f` is needed: if `f` is interval integrable
the two integrals split, and if it is not, then neither is the sum, so
both sides are `0` by the Bochner convention. -/
theorem integral_add_harmonic_eq {f : ℝ → ℝ} {w : ℝ} (r : ℝ) (k : ℤ)
    (hk : k ≠ 0) (hr : r = (k : ℝ)) :
    ∫ t in (0:ℝ)..1, (f t + w * Real.cos (2 * π * r * t)) =
      ∫ t in (0:ℝ)..1, f t := by
  have hg : IntervalIntegrable
      (fun t : ℝ => w * Real.cos (2 * π * r * t))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  by_cases hf : IntervalIntegrable f MeasureTheory.volume 0 1
  · rw [intervalIntegral.integral_add hf hg,
      intervalIntegral.integral_const_mul,
      integral_cos_two_pi_of_eq r k hk hr, mul_zero, add_zero]
  · have hfg : ¬ IntervalIntegrable
        (fun t : ℝ => f t + w * Real.cos (2 * π * r * t))
        MeasureTheory.volume 0 1 := by
      intro hsum
      have h2 := hsum.sub hg
      simp only [add_sub_cancel_right] at h2
      exact hf h2
    rw [intervalIntegral.integral_undef hf,
      intervalIntegral.integral_undef hfg]

/-! ### The expansion of the two-factor witness product -/

/-- **Product-to-sum expansion of the witness integrand.**  For every
real `u`,

`cos u · (1 + cos 3u) · (1 + cos 4u) = 1/4 + cos u + (3/4) cos 2u
  + (1/2) cos 3u + (1/2) cos 4u + (1/2) cos 5u + (1/4) cos 6u
  + (1/4) cos 8u`.

Only the five product-to-sum identities `cos u · cos u`,
`cos u · cos 3u`, `cos u · cos 4u`, `cos 3u · cos 4u` and
`cos u · cos 7u` are used.  The constant `1/4` is the constant term of
`cos²u / 2 = (1 + cos 2u)/4`, which arises inside
`cos u · (cos 3u · cos 4u)` because `cos 3u · cos 4u` returns a
`cos u` from the difference frequency `4 - 3 = 1`. -/
theorem cos_riesz_three_four (u : ℝ) :
    Real.cos u * ((1 + Real.cos (3 * u)) * (1 + Real.cos (4 * u))) =
      1 / 4 + Real.cos u + 3 / 4 * Real.cos (2 * u)
        + 1 / 2 * Real.cos (3 * u) + 1 / 2 * Real.cos (4 * u)
        + 1 / 2 * Real.cos (5 * u) + 1 / 4 * Real.cos (6 * u)
        + 1 / 4 * Real.cos (8 * u) := by
  have p11 : Real.cos u * Real.cos u =
      (1 + Real.cos (2 * u)) / 2 := by
    have h := cos_mul_cos_eq u u
    have a1 : u - u = 0 := by ring
    have a2 : u + u = 2 * u := by ring
    rw [a1, a2, Real.cos_zero] at h
    exact h
  have p13 : Real.cos u * Real.cos (3 * u) =
      (Real.cos (2 * u) + Real.cos (4 * u)) / 2 := by
    have h := cos_mul_cos_eq u (3 * u)
    have a1 : u - 3 * u = -(2 * u) := by ring
    have a2 : u + 3 * u = 4 * u := by ring
    rw [a1, a2, Real.cos_neg] at h
    exact h
  have p14 : Real.cos u * Real.cos (4 * u) =
      (Real.cos (3 * u) + Real.cos (5 * u)) / 2 := by
    have h := cos_mul_cos_eq u (4 * u)
    have a1 : u - 4 * u = -(3 * u) := by ring
    have a2 : u + 4 * u = 5 * u := by ring
    rw [a1, a2, Real.cos_neg] at h
    exact h
  have p17 : Real.cos u * Real.cos (7 * u) =
      (Real.cos (6 * u) + Real.cos (8 * u)) / 2 := by
    have h := cos_mul_cos_eq u (7 * u)
    have a1 : u - 7 * u = -(6 * u) := by ring
    have a2 : u + 7 * u = 8 * u := by ring
    rw [a1, a2, Real.cos_neg] at h
    exact h
  have p34 : Real.cos (3 * u) * Real.cos (4 * u) =
      (Real.cos u + Real.cos (7 * u)) / 2 := by
    have h := cos_mul_cos_eq (3 * u) (4 * u)
    have a1 : 3 * u - 4 * u = -u := by ring
    have a2 : 3 * u + 4 * u = 7 * u := by ring
    rw [a1, a2, Real.cos_neg] at h
    exact h
  linear_combination p13 + p14 + Real.cos u * p34 + p11 / 2 + p17 / 2

/-- The expansion of `cos_riesz_three_four`, written in exactly the
shape the master theorem's integrand takes at `n = 2`,
`m = sharpFreq`, `a ≡ 1`, `φ ≡ 0`, `K = 1`, `ψ = 0`. -/
theorem cos_mul_sharpProduct_eq (t : ℝ) :
    Real.cos (2 * π * ((1 : ℤ) : ℝ) * t + 0) *
        ∏ j ∈ range 2,
          (1 + (1 : ℝ) *
            Real.cos (2 * π * (sharpFreq j : ℝ) * t + 0)) =
      1 / 4 + 1 * Real.cos (2 * π * 1 * t)
        + 3 / 4 * Real.cos (2 * π * 2 * t)
        + 1 / 2 * Real.cos (2 * π * 3 * t)
        + 1 / 2 * Real.cos (2 * π * 4 * t)
        + 1 / 2 * Real.cos (2 * π * 5 * t)
        + 1 / 4 * Real.cos (2 * π * 6 * t)
        + 1 / 4 * Real.cos (2 * π * 8 * t) := by
  have h := cos_riesz_three_four (2 * π * t)
  have e0 : 2 * π * ((1 : ℤ) : ℝ) * t + 0 = 2 * π * t := by
    push_cast
    ring
  have e1 : 2 * π * (sharpFreq 0 : ℝ) * t + 0 = 3 * (2 * π * t) := by
    rw [sharpFreq_zero]
    push_cast
    ring
  have e2 : 2 * π * (sharpFreq 1 : ℝ) * t + 0 = 4 * (2 * π * t) := by
    rw [sharpFreq_one]
    push_cast
    ring
  have f1 : 2 * π * 1 * t = 2 * π * t := by ring
  have f2 : 2 * π * 2 * t = 2 * (2 * π * t) := by ring
  have f3 : 2 * π * 3 * t = 3 * (2 * π * t) := by ring
  have f4 : 2 * π * 4 * t = 4 * (2 * π * t) := by ring
  have f5 : 2 * π * 5 * t = 5 * (2 * π * t) := by ring
  have f6 : 2 * π * 6 * t = 6 * (2 * π * t) := by ring
  have f8 : 2 * π * 8 * t = 8 * (2 * π * t) := by ring
  rw [Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, e0, e1, e2, f2, f3, f4, f5, f6, f8, f1]
  linear_combination h

/-- The expanded integrand integrates to `1/4`: every one of its seven
harmonics has nonzero integer frequency and therefore mean `0` over
`[0, 1]`, leaving only the constant term. -/
theorem integral_sharp_expansion :
    ∫ t in (0:ℝ)..1,
        (1 / 4 + 1 * Real.cos (2 * π * 1 * t)
          + 3 / 4 * Real.cos (2 * π * 2 * t)
          + 1 / 2 * Real.cos (2 * π * 3 * t)
          + 1 / 2 * Real.cos (2 * π * 4 * t)
          + 1 / 2 * Real.cos (2 * π * 5 * t)
          + 1 / 4 * Real.cos (2 * π * 6 * t)
          + 1 / 4 * Real.cos (2 * π * 8 * t)) = 1 / 4 := by
  rw [integral_add_harmonic_eq (r := 8) (k := 8)
      (hk := by norm_num) (hr := by norm_num),
    integral_add_harmonic_eq (r := 6) (k := 6)
      (hk := by norm_num) (hr := by norm_num),
    integral_add_harmonic_eq (r := 5) (k := 5)
      (hk := by norm_num) (hr := by norm_num),
    integral_add_harmonic_eq (r := 4) (k := 4)
      (hk := by norm_num) (hr := by norm_num),
    integral_add_harmonic_eq (r := 3) (k := 3)
      (hk := by norm_num) (hr := by norm_num),
    integral_add_harmonic_eq (r := 2) (k := 2)
      (hk := by norm_num) (hr := by norm_num),
    integral_add_harmonic_eq (r := 1) (k := 1)
      (hk := by norm_num) (hr := by norm_num),
    intervalIntegral.integral_const]
  norm_num

/-! ### The counterexample integral -/

/-- **The witness integral.**  With frequencies `sharpFreq` (that is
`3, 4, 8, 16, …`), amplitudes `a ≡ 1`, phases `φ ≡ 0`, probe `K = 1`
and `ψ = 0`, the first two factors already give

`∫ t in 0..1, cos (2π t) · (1 + cos (6π t)) · (1 + cos (8π t)) = 1/4`.

The headroom hypothesis of
`integral_cos_mul_rieszProduct_of_add_sum_le` fails here
(`not_add_sum_le_sharpFreq`), so that theorem does not apply; the
*weakened* statement, which asks only for plain super-increasingness
and `|K| < m 0`, would force the value `0` at `K = 1 ≠ 0`. -/
theorem integral_cos_mul_sharpProduct :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * ((1 : ℤ) : ℝ) * t + 0) *
        ∏ j ∈ range 2,
          (1 + (1 : ℝ) *
            Real.cos (2 * π * (sharpFreq j : ℝ) * t + 0)) =
      1 / 4 := by
  rw [intervalIntegral.integral_congr (g := fun t =>
      1 / 4 + 1 * Real.cos (2 * π * 1 * t)
        + 3 / 4 * Real.cos (2 * π * 2 * t)
        + 1 / 2 * Real.cos (2 * π * 3 * t)
        + 1 / 2 * Real.cos (2 * π * 4 * t)
        + 1 / 2 * Real.cos (2 * π * 5 * t)
        + 1 / 4 * Real.cos (2 * π * 6 * t)
        + 1 / 4 * Real.cos (2 * π * 8 * t))
      (fun t _ => cos_mul_sharpProduct_eq t)]
  exact integral_sharp_expansion

/-- The witness integral is not `0`.  The headroom hypothesis of
`integral_cos_mul_rieszProduct_of_add_sum_le` fails here, so that
theorem does not apply; `0` is the value the *weakened* statement
would force at the probe `K = 1 ≠ 0`. -/
theorem integral_cos_mul_sharpProduct_ne_zero :
    ∫ t in (0:ℝ)..1, Real.cos (2 * π * ((1 : ℤ) : ℝ) * t + 0) *
        ∏ j ∈ range 2,
          (1 + (1 : ℝ) *
            Real.cos (2 * π * (sharpFreq j : ℝ) * t + 0)) ≠ 0 := by
  rw [integral_cos_mul_sharpProduct]
  norm_num

/-- **Capstone: the headroom offset cannot be dropped.**

There are a factor count `n`, integer frequencies `m` that are
super-increasing in the plain sense `∀ j, ∑_{i<j} m i < m j`,
amplitudes `a`, phases `φ`, a phase `ψ`, and a probe frequency
`K ≠ 0` below the spectral floor, `|K| < m 0`, for which

`∫ t in 0..1, cos (2π K t + ψ) ·
  ∏_{j<n} (1 + a j · cos (2π (m j) t + φ j))`

is **not** equal to `if K = 0 then cos ψ else 0` — here that forced
value is `0`, while the integral is `1/4`
(`integral_cos_mul_sharpProduct`).

So the conclusion of `integral_cos_mul_rieszProduct_of_add_sum_le`
does not follow from plain super-increasingness together with
`|K| < m 0`: the offset `m 0` in its hypothesis
`∀ j, m 0 + ∑_{i<j} m i ≤ m j` cannot be deleted.  This is a single
witness and says nothing more: it does not show that the headroom
hypothesis is the weakest `K`-free hypothesis yielding the
conclusion. -/
theorem exists_superIncreasing_probe_integral_ne :
    ∃ (n : ℕ) (m : ℕ → ℕ) (a φ : ℕ → ℝ) (K : ℤ) (ψ : ℝ),
      (∀ j, ∑ i ∈ range j, m i < m j) ∧ K.natAbs < m 0 ∧ K ≠ 0 ∧
        ∫ t in (0:ℝ)..1, Real.cos (2 * π * (K : ℝ) * t + ψ) *
            ∏ j ∈ range n,
              (1 + a j *
                Real.cos (2 * π * (m j : ℝ) * t + φ j)) ≠
          (if K = 0 then Real.cos ψ else 0) := by
  refine ⟨2, sharpFreq, fun _ => 1, fun _ => 0, 1, 0,
    superIncreasing_sharpFreq, natAbs_one_lt_sharpFreq_zero,
    (by norm_num), ?_⟩
  show ∫ t in (0:ℝ)..1, Real.cos (2 * π * ((1 : ℤ) : ℝ) * t + 0) *
      ∏ j ∈ range 2,
        (1 + (1 : ℝ) *
          Real.cos (2 * π * (sharpFreq j : ℝ) * t + 0)) ≠
    (if (1 : ℤ) = 0 then Real.cos 0 else 0)
  rw [if_neg (by norm_num : (1 : ℤ) ≠ 0)]
  exact integral_cos_mul_sharpProduct_ne_zero

end Fabius
