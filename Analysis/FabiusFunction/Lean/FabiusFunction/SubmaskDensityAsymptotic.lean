import FabiusFunction.DigitalDensity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The submask counting function and its density

`DigitalDensity` counts, inside a *full* dyadic block, the naturals
whose binary expansion contains a fixed mask `d`:

`#{n < 2^m | bitSupport d ⊆ bitSupport n} = 2^{m - w(d)}`.

The exponent-sequence volume needs the same count over an *arbitrary*
initial segment, where it appears as the sparse-Prouhet density

`ω_d(L) = 2^{-w(d)} L + O_d(1)`,

`ω_d(L)` being the number of `h < L` with `C(h, d)` odd.  This module
proves that, with an explicit constant and no asymptotic notation:
the indicator of the submask condition is `2^m`-periodic whenever
`d < 2^m`, so the count over `L` splits into `⌊L/2^m⌋` full blocks
plus a partial block that is bounded by a full one.  Both the error
and its two-sided bound are exact:

`|2^{w(d)} · ω_d(L) - L| ≤ 2^m`  for every `L`,

which at `m = d` (via `d < 2^d`) is a bound depending on `d` alone.
Dividing by `L` and letting `L → ∞` gives the density itself.

The periodicity comes from `Nat.testBit_two_pow_mul_add`: adding a
multiple of `2^m` leaves every bit below `m` alone, and all of `d`'s
bits lie below `m`.

* `submaskCount` — the counting function `ω_d`;
* `bitSupport_subset_two_pow_mul_add_iff` — **periodicity**;
* `submaskCount_two_pow_mul` — the full-block count, `k · 2^{m-w(d)}`;
* `abs_two_pow_weight_mul_submaskCount_sub_le` — **the exact error
  bound**, and `..._self` its hypothesis-free reading;
* `tendsto_submaskCount_div_atTop` — **the density** `2^{-w(d)}`;
* `tendsto_card_filter_odd_choose_div_atTop` — the Lucas reading,
  the volume's `ω_d(L)/L → 2^{-s₂(d)}`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- **The submask counting function.**  `submaskCount d L` is the
number of naturals below `L` whose binary expansion contains every
one-bit of `d`.  Through the Lucas criterion it is equally the number
of `n < L` with `C(n, d)` odd. -/
noncomputable def submaskCount (d L : ℕ) : ℕ :=
  #({n ∈ range L | bitSupport d ⊆ bitSupport n})

/-- No natural numbers occur in the empty initial segment. -/
@[simp] theorem submaskCount_zero (d : ℕ) : submaskCount d 0 = 0 := by
  simp [submaskCount]

/-- The counting function is monotone in the length of the segment. -/
theorem submaskCount_mono (d : ℕ) {L L' : ℕ} (h : L ≤ L') :
    submaskCount d L ≤ submaskCount d L' :=
  Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- The full-block count, restated from `DigitalDensity`. -/
theorem submaskCount_two_pow {m d : ℕ} (hd : d < 2 ^ m) :
    submaskCount d (2 ^ m) = 2 ^ (m - binaryWeight d) :=
  card_filter_bitSupport_subset m hd

/-- A mask below `2 ^ m` has at most `m` one-bits. -/
theorem binaryWeight_le_of_lt_two_pow {m d : ℕ} (hd : d < 2 ^ m) :
    binaryWeight d ≤ m := by
  have hsub : bitSupport d ⊆ range m :=
    (bitSupport_subset_range_iff_lt_two_pow d m).mpr hd
  have hcard := Finset.card_le_card hsub
  rwa [card_bitSupport, Finset.card_range] at hcard

/-- Bits below `m` are untouched by adding a multiple of `2 ^ m`. -/
private theorem mem_bitSupport_two_pow_mul_add {m i : ℕ}
    (hi : i < 2 ^ m) (k : ℕ) {j : ℕ} (hj : j < m) :
    j ∈ bitSupport (2 ^ m * k + i) ↔ j ∈ bitSupport i := by
  rw [mem_bitSupport, mem_bitSupport,
    Nat.testBit_two_pow_mul_add k hi j, if_pos hj]

/-- **Periodicity of the submask condition.**  For a mask `d` below
`2 ^ m`, containment of `d` is unchanged by adding any multiple of
`2 ^ m` to a residue `i < 2 ^ m`: every bit of `d` lies below `m`,
and those bits are the ones the addition leaves alone. -/
theorem bitSupport_subset_two_pow_mul_add_iff {m d : ℕ}
    (hd : d < 2 ^ m) {i : ℕ} (hi : i < 2 ^ m) (k : ℕ) :
    bitSupport d ⊆ bitSupport (2 ^ m * k + i) ↔
      bitSupport d ⊆ bitSupport i := by
  have hsub : bitSupport d ⊆ range m :=
    (bitSupport_subset_range_iff_lt_two_pow d m).mpr hd
  constructor
  · exact fun h j hj =>
      (mem_bitSupport_two_pow_mul_add hi k
        (mem_range.mp (hsub hj))).mp (h hj)
  · exact fun h j hj =>
      (mem_bitSupport_two_pow_mul_add hi k
        (mem_range.mp (hsub hj))).mpr (h hj)

/-- A partial block sitting on top of a whole number of full blocks
contributes exactly what the same partial block contributes at the
origin. -/
theorem submaskCount_two_pow_mul_add {m d : ℕ} (hd : d < 2 ^ m)
    (k : ℕ) {s : ℕ} (hs : s ≤ 2 ^ m) :
    submaskCount d (2 ^ m * k + s) =
      submaskCount d (2 ^ m * k) + submaskCount d s := by
  classical
  simp only [submaskCount, Finset.card_filter]
  rw [Finset.sum_range_add]
  refine congrArg _ (Finset.sum_congr rfl fun i hi => ?_)
  have hi' : i < 2 ^ m := lt_of_lt_of_le (mem_range.mp hi) hs
  exact if_congr (bitSupport_subset_two_pow_mul_add_iff hd hi' k) rfl rfl

/-- **The full-block count over `k` blocks.**  Density `2^{-w(d)}` is
exact on any whole number of dyadic blocks. -/
theorem submaskCount_two_pow_mul {m d : ℕ} (hd : d < 2 ^ m) (k : ℕ) :
    submaskCount d (2 ^ m * k) = k * 2 ^ (m - binaryWeight d) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := submaskCount_two_pow_mul_add hd k (le_refl (2 ^ m))
      rw [show 2 ^ m * (k + 1) = 2 ^ m * k + 2 ^ m by ring, hstep, ih,
        submaskCount_two_pow hd]
      ring

/-- **The exact error bound.**  For a mask `d` below `2 ^ m`, the
count over any initial segment differs from the ideal density count
by at most one full block:

`|2^{w(d)} · submaskCount d L - L| ≤ 2^m`.

This is the volume's `ω_d(L) = 2^{-s₂(d)} L + O_d(1)` with the
implied constant made explicit. -/
theorem abs_two_pow_weight_mul_submaskCount_sub_le {m d : ℕ}
    (hd : d < 2 ^ m) (L : ℕ) :
    |(2 ^ binaryWeight d * submaskCount d L : ℤ) - L| ≤ 2 ^ m := by
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  set k := L / 2 ^ m with hk
  set s := L % 2 ^ m with hsdef
  have hL : 2 ^ m * k + s = L := Nat.div_add_mod L (2 ^ m)
  have hs : s < 2 ^ m := Nat.mod_lt _ hpos
  have hw : binaryWeight d ≤ m := binaryWeight_le_of_lt_two_pow hd
  have hpow : 2 ^ binaryWeight d * 2 ^ (m - binaryWeight d) = 2 ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' hw]
  have hcount : submaskCount d L =
      k * 2 ^ (m - binaryWeight d) + submaskCount d s := by
    rw [← hL, submaskCount_two_pow_mul_add hd k hs.le,
      submaskCount_two_pow_mul hd]
  have hsplit : 2 ^ binaryWeight d * (k * 2 ^ (m - binaryWeight d))
      = 2 ^ m * k := by
    rw [← hpow]; ring
  have hNat : 2 ^ binaryWeight d * submaskCount d L
      = 2 ^ m * k + 2 ^ binaryWeight d * submaskCount d s := by
    rw [hcount, Nat.mul_add, hsplit]
  have h1 : (2 : ℤ) ^ binaryWeight d * (submaskCount d L : ℤ)
      = 2 ^ m * (k : ℤ) + 2 ^ binaryWeight d * (submaskCount d s : ℤ) := by
    exact_mod_cast hNat
  have h2 : (L : ℤ) = 2 ^ m * (k : ℤ) + (s : ℤ) := by
    exact_mod_cast hL.symm
  have key : (2 ^ binaryWeight d * submaskCount d L : ℤ) - L
      = 2 ^ binaryWeight d * (submaskCount d s : ℤ) - (s : ℤ) := by
    push_cast
    push_cast at h1
    rw [h1, h2]
    ring
  have hcs : submaskCount d s ≤ 2 ^ (m - binaryWeight d) := by
    have hmono := submaskCount_mono d hs.le
    rwa [submaskCount_two_pow hd] at hmono
  have hAB : (2 : ℤ) ^ binaryWeight d * (submaskCount d s : ℤ) ≤ 2 ^ m := by
    have hNatB : 2 ^ binaryWeight d * submaskCount d s ≤ 2 ^ m :=
      hpow ▸ Nat.mul_le_mul_left _ hcs
    exact_mod_cast hNatB
  have hA0 : (0 : ℤ) ≤ 2 ^ binaryWeight d * (submaskCount d s : ℤ) := by
    positivity
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  have hsB : (s : ℤ) < 2 ^ m := by exact_mod_cast hs
  rw [key, abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- The hypothesis-free reading, at `m = d` via `d < 2 ^ d`: the error
constant depends on the mask alone. -/
theorem abs_two_pow_weight_mul_submaskCount_sub_le_self (d L : ℕ) :
    |(2 ^ binaryWeight d * submaskCount d L : ℤ) - L| ≤ 2 ^ d :=
  abs_two_pow_weight_mul_submaskCount_sub_le d.lt_two_pow_self L

/-- The error bound in real division form: the empirical density
differs from `2^{-w(d)}` by at most `(2^m / 2^{w(d)}) / L`. -/
theorem abs_submaskCount_div_sub_le {m d : ℕ} (hd : d < 2 ^ m)
    {L : ℕ} (hL : 0 < L) :
    |(submaskCount d L : ℝ) / L - (2 : ℝ)⁻¹ ^ binaryWeight d|
      ≤ ((2 : ℝ) ^ m / 2 ^ binaryWeight d) / L := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hden : (0 : ℝ) < 2 ^ binaryWeight d * (L : ℝ) := by positivity
  have habs : |(2 : ℝ) ^ binaryWeight d * (submaskCount d L : ℝ) - (L : ℝ)|
      ≤ (2 : ℝ) ^ m := by
    have hZ := abs_two_pow_weight_mul_submaskCount_sub_le hd L
    rw [abs_sub_le_iff] at hZ
    obtain ⟨hZu, hZl⟩ := hZ
    have hu : (((2 ^ binaryWeight d * submaskCount d L : ℤ) - (L : ℤ)) : ℝ)
        ≤ (((2 : ℤ) ^ m : ℤ) : ℝ) := by exact_mod_cast hZu
    have hl : (((L : ℤ) - (2 ^ binaryWeight d * submaskCount d L : ℤ)) : ℝ)
        ≤ (((2 : ℤ) ^ m : ℤ) : ℝ) := by exact_mod_cast hZl
    push_cast at hu hl
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hkey : (submaskCount d L : ℝ) / L - (2 : ℝ)⁻¹ ^ binaryWeight d
      = ((2 : ℝ) ^ binaryWeight d * (submaskCount d L : ℝ) - (L : ℝ))
          / (2 ^ binaryWeight d * (L : ℝ)) := by
    rw [inv_pow]
    field_simp
  rw [hkey, abs_div, abs_of_pos hden, div_div]
  gcongr

/-- **The digital density as a limit.**  The proportion of naturals
below `L` containing the mask of `d` converges to `2^{-w(d)}`. -/
theorem tendsto_submaskCount_div_atTop {m d : ℕ} (hd : d < 2 ^ m) :
    Tendsto (fun L : ℕ => (submaskCount d L : ℝ) / L) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ binaryWeight d)) := by
  have h0 : Tendsto
      (fun L : ℕ => (submaskCount d L : ℝ) / L - (2 : ℝ)⁻¹ ^ binaryWeight d)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (tendsto_const_div_atTop_nhds_zero_nat
        ((2 : ℝ) ^ m / 2 ^ binaryWeight d))
    filter_upwards [eventually_gt_atTop 0] with L hL
    rw [Real.norm_eq_abs]
    exact abs_submaskCount_div_sub_le hd hL
  simpa using h0.add_const ((2 : ℝ)⁻¹ ^ binaryWeight d)

/-- The hypothesis-free reading of the density. -/
theorem tendsto_submaskCount_div_atTop_self (d : ℕ) :
    Tendsto (fun L : ℕ => (submaskCount d L : ℝ) / L) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ binaryWeight d)) :=
  tendsto_submaskCount_div_atTop d.lt_two_pow_self

/-- The Lucas reading of the counting function: `submaskCount d L` is
the number of odd binomial coefficients `C(n, d)` with `n < L`. -/
theorem submaskCount_eq_card_filter_odd_choose (d L : ℕ) :
    submaskCount d L = #({n ∈ range L | Odd (n.choose d)}) := by
  classical
  rw [submaskCount]
  exact congrArg _
    (Finset.filter_congr fun n _ => (odd_choose_iff_bitSupport_subset n d).symm)

/-- **The sparse-Prouhet density.**  Among `n < L`, the proportion
with `C(n, d)` odd converges to `2^{-s₂(d)}`.  This is the volume's
`ω_d(L) = 2^{-s₂(d)} L + O_d(1)`, in its limiting form; the effective
form with the constant `2^d` exhibited is
`abs_two_pow_weight_mul_submaskCount_sub_le_self`. -/
theorem tendsto_card_filter_odd_choose_div_atTop (d : ℕ) :
    Tendsto
      (fun L : ℕ => (#({n ∈ range L | Odd (n.choose d)}) : ℝ) / L) atTop
      (𝓝 ((2 : ℝ)⁻¹ ^ binaryWeight d)) := by
  simpa [submaskCount_eq_card_filter_odd_choose] using
    tendsto_submaskCount_div_atTop_self d

end Fabius
