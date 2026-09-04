import FabiusFunction.HalfIntegerAliasIdentity
import FabiusFunction.SincPrefixBound
import FabiusFunction.IntSumFolding
import Mathlib.Analysis.PSeries

/-!
# A certified bound for the aliasing error

The spectra volume's `p1:thm:alias-error`: the folded coefficient `A_{N,r}`
differs from the target amplitude `Û(r/2)` only by the alias terms `q ≠ 0`
of `A_{N,r} = ∑_q Û(qN + r/2)`, and each of those is controlled by the
corpus's sinc-prefix bound `‖Û(x)‖ ≤ C_K / |x|^K`, `C_K = 2^{K(K-1)/2}/π^K`.
For `r < N` every alias point satisfies `|qN + r/2| ≥ N|q|/2`, so

`‖A_{N,r} - Û(r/2)‖ ≤ C_K (2/N)^K ∑_{q ∈ ℤ} |q|^{-K}
                    = 2^{K+1} C_K N^{-K} ∑_{n ≥ 1} n^{-K}`.

The volume's constant is `2 (2^K - 1) ζ(K)` in place of `2^{K+1} ζ(K)`: it
sums only over the odd integers `2q - 1` that the bound `|q| N/2` really
produces.  The version here is the simpler bound with the full zeta sum;
it holds for every `K ≥ 2`, every `N ≥ 1` and every residue `r < N`, with
no parity assumption on `r` and no restriction to `N = 2^n`.

## Main declarations

* `abs_alias_point_ge` — `|qN + r/2| ≥ N|q|/2` for `q ≠ 0`, `r < N`.
* `norm_alias_term_le` — each alias term is at most `C_K (2/N)^K |q|^{-K}`.
* `norm_foldedCoefficient_sub_le` — **`p1:thm:alias-error`**, tsum form.
* `norm_foldedCoefficient_sub_le'` — the same with the zeta-type constant.
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-- The alias points stay away from zero: for `q ≠ 0` and `0 ≤ c < N/2`,
`|qN + c| ≥ N|q|/2`. -/
theorem abs_alias_point_ge {N c : ℝ} (hN : 0 < N) (hc0 : 0 ≤ c) (hc : c < N / 2)
    {q : ℤ} (hq : q ≠ 0) : N * |(q : ℝ)| / 2 ≤ |(q : ℝ) * N + c| := by
  have h1 : (1 : ℝ) ≤ |(q : ℝ)| := by exact_mod_cast Int.one_le_abs hq
  have h2 : |(q : ℝ) * N| - |c| ≤ |(q : ℝ) * N + c| := by
    have := abs_sub_abs_le_abs_sub ((q : ℝ) * N) (-c)
    rwa [abs_neg, sub_neg_eq_add] at this
  rw [abs_mul, abs_of_pos hN, abs_of_nonneg hc0] at h2
  nlinarith

/-- Each alias term is bounded by the sinc-prefix bound at the alias point:
`‖Û(qN + r/2)‖ ≤ C_K (2/N)^K |q|^{-K}` for `q ≠ 0`. -/
theorem norm_alias_term_le (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N]
    {r : ZMod (2 * N)} (hr : r.val < N) (K : ℕ) {q : ℤ} (hq : q ≠ 0) :
    ‖rvachevFourier F ((q : ℂ) * N + (r.val : ℂ) / 2)‖ ≤
      (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K * |(q : ℝ)| ^ (-(K : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : (0 : ℝ) ≤ (r.val : ℝ) / 2 := by positivity
  have hc : (r.val : ℝ) / 2 < N / 2 := by
    have : (r.val : ℝ) < N := by exact_mod_cast hr
    linarith
  have hge := abs_alias_point_ge hNpos hc0 hc hq
  have hq1 : (1 : ℝ) ≤ |(q : ℝ)| := by exact_mod_cast Int.one_le_abs hq
  set x : ℝ := (q : ℝ) * N + (r.val : ℝ) / 2 with hx
  have hxpos : 0 < |x| := by
    have : 0 < N * |(q : ℝ)| / 2 := by positivity
    linarith
  have hxne : x ≠ 0 := abs_pos.mp hxpos
  have harg : ((q : ℂ) * N + (r.val : ℂ) / 2) = ((x : ℝ) : ℂ) := by
    rw [hx]
    push_cast
    ring
  rw [harg, rvachevFourier_eq_product F hF]
  refine (norm_rvachevFourierProduct_le_prefix_div K hxne).trans ?_
  -- `C_K / (π|x|)^K ≤ C_K / (π N|q|/2)^K`, since `|x| ≥ N|q|/2`
  have hden : (Real.pi * (N * |(q : ℝ)| / 2)) ^ K ≤ (Real.pi * |x|) ^ K :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hge Real.pi_pos.le) K
  have hpos1 : 0 < (Real.pi * (N * |(q : ℝ)| / 2)) ^ K := by positivity
  have hqpos : 0 < |(q : ℝ)| := by linarith
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc (2 : ℝ) ^ (K.choose 2) / (Real.pi * |x|) ^ K
      ≤ (2 : ℝ) ^ (K.choose 2) / (Real.pi * (N * |(q : ℝ)| / 2)) ^ K :=
        div_le_div_of_nonneg_left (by positivity) hpos1 hden
    _ = (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K * |(q : ℝ)| ^ (-(K : ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg _), Real.rpow_natCast, mul_pow, div_pow, mul_pow,
          div_pow]
        field_simp

/-- **`p1:thm:alias-error`, tsum form.**  For every `K ≥ 2`, `N ≥ 1` and residue
`r` with `r < N`,

`‖A_{N,r} - Û(r/2)‖ ≤ C_K (2/N)^K ∑_{q∈ℤ} |q|^{-K}`. -/
theorem norm_foldedCoefficient_sub_le (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N]
    {r : ZMod (2 * N)} (hr : r.val < N) {K : ℕ} (hK : 2 ≤ K) :
    ‖foldedCoefficient F N r - rvachevFourier F ((r.val : ℂ) / 2)‖ ≤
      (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K *
        ∑' q : ℤ, |(q : ℝ)| ^ (-(K : ℝ)) := by
  set f : ℤ → ℂ := fun q => rvachevFourier F ((q : ℂ) * N + (r.val : ℂ) / 2) with hf
  set f' : ℤ → ℂ := fun q => if q = 0 then 0 else f q with hf'
  set g : ℤ → ℝ := fun q =>
    (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K * |(q : ℝ)| ^ (-(K : ℝ)) with hg
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hgsum : HasSum g ((2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K *
      ∑' q : ℤ, |(q : ℝ)| ^ (-(K : ℝ))) :=
    (Real.summable_abs_int_rpow hK1).hasSum.mul_left _
  have hbound : ∀ q : ℤ, ‖f' q‖ ≤ g q := by
    intro q
    by_cases hq : q = 0
    · have hKne : -(K : ℝ) ≠ 0 := by
        have : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
        exact neg_ne_zero.mpr this
      simp only [hf', hg, hq, Int.cast_zero, abs_zero]
      rw [Real.zero_rpow hKne]
      simp
    · simp only [hf', if_neg hq]
      exact norm_alias_term_le F hF N hr K hq
  have hf'sum : Summable f' := Summable.of_norm_bounded hgsum.summable hbound
  -- `f = f' + (single at 0)`, so `∑' f = ∑' f' + f 0`
  have hsplit : foldedCoefficient F N r = (∑' q : ℤ, f' q) + f 0 := by
    rw [foldedCoefficient_eq_tsum F hF N r]
    have hdec : f = fun q => f' q + (if q = 0 then f 0 else 0) := by
      funext q
      by_cases hq : q = 0
      · simp [hf', hq]
      · simp [hf', hq]
    have hsingle : Summable fun q : ℤ => if q = 0 then f 0 else 0 :=
      (hasSum_ite_eq (0 : ℤ) (f 0)).summable
    change ∑' q : ℤ, f q = _
    conv_lhs => rw [hdec]
    simp only []
    rw [Summable.tsum_add hf'sum hsingle, tsum_ite_eq]
  have hf0 : f 0 = rvachevFourier F ((r.val : ℂ) / 2) := by
    simp [hf]
  rw [hsplit, hf0, add_sub_cancel_right]
  exact tsum_of_norm_bounded hgsum hbound

/-- The alias sum as a zeta-type constant: `∑_{q∈ℤ} |q|^{-K} = 2 ∑_{n≥1} n^{-K}`. -/
theorem tsum_abs_int_rpow_eq {K : ℕ} (hK : 2 ≤ K) :
    ∑' q : ℤ, |(q : ℝ)| ^ (-(K : ℝ)) = 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(K : ℝ)) := by
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hs := Real.summable_abs_int_rpow hK1
  have heven : ∀ k : ℤ, |((-k : ℤ) : ℝ)| ^ (-(K : ℝ)) = |(k : ℝ)| ^ (-(K : ℝ)) := by
    intro k
    rw [Int.cast_neg, abs_neg]
  rw [IntSum.tsum_eq_zero_add_two_mul_tsum_add_one hs heven]
  have hKne : -(K : ℝ) ≠ 0 := by
    have : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
    exact neg_ne_zero.mpr this
  have h0 : |((0 : ℤ) : ℝ)| ^ (-(K : ℝ)) = 0 := by
    rw [Int.cast_zero, abs_zero, Real.zero_rpow hKne]
  rw [h0, zero_add]
  congr 1
  refine tsum_congr fun n => ?_
  rw [show (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
    abs_of_nonneg (by positivity)]

/-- **`p1:thm:alias-error`** with the zeta-type constant:
`‖A_{N,r} - Û(r/2)‖ ≤ 2^{K+1} C_K N^{-K} ∑_{n≥1} n^{-K}`. -/
theorem norm_foldedCoefficient_sub_le' (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) [NeZero N]
    {r : ZMod (2 * N)} (hr : r.val < N) {K : ℕ} (hK : 2 ≤ K) :
    ‖foldedCoefficient F N r - rvachevFourier F ((r.val : ℂ) / 2)‖ ≤
      2 * (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K *
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(K : ℝ)) := by
  have h := norm_foldedCoefficient_sub_le F hF N hr hK
  rw [tsum_abs_int_rpow_eq hK] at h
  calc ‖foldedCoefficient F N r - rvachevFourier F ((r.val : ℂ) / 2)‖
      ≤ (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K *
          (2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(K : ℝ))) := h
    _ = 2 * (2 : ℝ) ^ (K.choose 2) / Real.pi ^ K * (2 / (N : ℝ)) ^ K *
          ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(K : ℝ)) := by ring

/-! ## Convergence of the folded coefficients to the sinc product

The volume's `p1:thm:q-approximant` closes with the statement that, for a fixed
odd `r`, the finite `q`-binomial approximant converges to `Φ(r/2)` as the level
grows.  That follows from the alias error bound above at any fixed order: the
bound decays like `N^{-K}`, and `K = 2` already suffices for the limit. -/

/-- **The alias approximants converge.**  For every fixed `r`, the folded
coefficients at dyadic modulus converge to the sinc-product value `Φ(r/2)`.

The sharp rate `E_n` of the volume is not claimed here: the bound used is the
fixed-order one, which gives `O(4^{-n})`. -/
theorem tendsto_foldedCoefficient_two_pow (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => foldedCoefficient F (2 ^ n) ((r : ℕ) : ZMod (2 * 2 ^ n)))
      Filter.atTop (nhds (rvachevFourier F ((r : ℂ) / 2))) := by
  set C : ℝ := 2 * (2 : ℝ) ^ (Nat.choose 2 2) / Real.pi ^ 2 *
      ∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)) with hC
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n : ℕ => C * (2 / (2 : ℝ) ^ n) ^ 2)
    (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop r] with n hn
    haveI : NeZero (2 ^ n) := ⟨by positivity⟩
    have hrn : r < 2 ^ n := lt_of_lt_of_le hn (Nat.le_of_lt Nat.lt_two_pow_self)
    have hval : ((r : ℕ) : ZMod (2 * 2 ^ n)).val = r := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h := norm_foldedCoefficient_sub_le' F hF (2 ^ n)
      (r := ((r : ℕ) : ZMod (2 * 2 ^ n))) (by rw [hval]; exact hrn) (K := 2) le_rfl
    rw [hval] at h
    have hcast : (((2 ^ n : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    rw [hcast] at h
    refine h.trans (le_of_eq ?_)
    rw [hC]
    ring
  · have hgeom : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
      have hpow : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have heq : (fun n : ℕ => (2 : ℝ) / 2 ^ n) = fun n : ℕ => 2 * ((1 : ℝ) / 2) ^ n := by
        funext n
        rw [one_div, inv_pow, div_eq_mul_inv]
      rw [heq]
      simpa using hpow.const_mul (2 : ℝ)
    have hsq : Filter.Tendsto (fun n : ℕ => (2 / (2 : ℝ) ^ n) ^ 2) Filter.atTop (nhds 0) := by
      simpa using hgeom.pow 2
    simpa using hsq.const_mul C

end Fabius
