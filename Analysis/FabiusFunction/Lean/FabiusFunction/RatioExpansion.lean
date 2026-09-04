import FabiusFunction.GeometricSimplexSum
import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.QPochhammerInfiniteBounds
import FabiusFunction.GaussianBinomialBounds
import FabiusFunction.GeneralQConditionNumber
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Cauchy products of power series and the ratio expansion

Regrouping the absolutely convergent multiple series `∑_{i : Fin m → ℕ} ∏_k g k (i k)` by the
total degree `∑_k i_k = N` (`hasSum_regroup_antidiagonalTuple`) turns the product formula
`hasSum_prod_fin_pi` into the **Cauchy product of `m` power series**
(`hasSum_prod_powerSeries`):

`∏_k ∑_n c_k(n) z^n = ∑_N (∑_{i_1+⋯+i_m = N} ∏_k c_k(i_k)) z^N`.

Applied to Euler's two expansions `(az;q)_∞ = ∑ (-1)^u q^{C(u,2)} a^u z^u/(q;q)_u` and
`1/(bz;q)_∞ = ∑ b^v z^v/(q;q)_v` (`‖bz‖ < 1`) this gives the **ratio expansion**

`∏_i (a_i z;q)_∞ / ∏_j (b_j z;q)_∞ = ∑_N c_N z^N`,

`c_N = ∑_{u_1+⋯+u_r+v_1+⋯+v_s = N} ∏_i (-1)^{u_i} q^{C(u_i,2)} a_i^{u_i}/(q;q)_{u_i}
  ∏_j b_j^{v_j}/(q;q)_{v_j}`,

the `r + s` coefficient sequences being concatenated with `Fin.append`.

## Main declarations

* `hasSum_regroup_antidiagonalTuple`, `hasSum_prod_powerSeries`.
* `summable_norm_euler_product_term`, `summable_norm_euler_reciprocal_term`.
* `hasSum_ratio_expansion`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Regrouping by total degree**: a convergent series over `Fin m → ℕ` may be summed fibrewise
over the finite sets `∑_k i_k = N`. -/
theorem hasSum_regroup_antidiagonalTuple {m : ℕ} {F : (Fin m → ℕ) → 𝕜} {S : 𝕜}
    (hF : HasSum F S) :
    HasSum (fun N : ℕ => ∑ i ∈ Finset.Nat.antidiagonalTuple m N, F i) S := by
  let e := Equiv.sigmaFiberEquiv (fun i : Fin m → ℕ => ∑ k, i k)
  have h1 : HasSum (F ∘ e) S := e.hasSum_iff.mpr hF
  refine h1.sigma fun N => ?_
  have hs : HasSum ({i : Fin m → ℕ | ∑ k, i k = N}.indicator F)
      (∑ i ∈ Finset.Nat.antidiagonalTuple m N, F i) := by
    have h3 : HasSum ({i : Fin m → ℕ | ∑ k, i k = N}.indicator F)
        (∑ b ∈ Finset.Nat.antidiagonalTuple m N, {i : Fin m → ℕ | ∑ k, i k = N}.indicator F b) :=
      hasSum_sum_of_ne_finset_zero fun b hb =>
        Set.indicator_of_notMem (by simpa [Finset.Nat.mem_antidiagonalTuple] using hb) F
    rwa [Finset.sum_congr rfl fun b hb =>
      Set.indicator_of_mem (by simpa [Finset.Nat.mem_antidiagonalTuple] using hb) F] at h3
  have h5 := hasSum_subtype_iff_indicator.mpr hs
  exact h5.congr_fun fun c => rfl

/-- **Cauchy product of finitely many power series**: if each `∑_n c_k(n) z^n` converges
absolutely, then `∏_k ∑_n c_k(n) z^n = ∑_N (∑_{i_1+⋯+i_m=N} ∏_k c_k(i_k)) z^N`. -/
theorem hasSum_prod_powerSeries {m : ℕ} (c : Fin m → ℕ → 𝕜) (z : 𝕜)
    (hc : ∀ k, Summable fun n => ‖c k n * z ^ n‖) :
    HasSum (fun N : ℕ => (∑ i ∈ Finset.Nat.antidiagonalTuple m N, ∏ k, c k (i k)) * z ^ N)
      (∏ k, ∑' n, c k n * z ^ n) := by
  obtain ⟨h, -⟩ := hasSum_prod_fin_pi m (fun k n => c k n * z ^ n) hc
  refine (hasSum_regroup_antidiagonalTuple h).congr_fun fun N => ?_
  rw [sum_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at hi
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, hi]

omit [CompleteSpace 𝕜] in
/-- The terms of Euler's product expansion are norm-summable for every `w`. -/
theorem summable_norm_euler_product_term {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Summable fun u : ℕ =>
      ‖(-1 : 𝕜) ^ u * q ^ u.choose 2 / finiteQPochhammerIn q q u * w ^ u‖ := by
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have hq1 : ‖q‖ < 1 := hq
  have hP : 0 < qPochhammerInfIn ‖q‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg q) hq1 (norm_nonneg q) hq1
  -- the real Euler series at `(‖q‖, -‖w‖)` has nonnegative terms
  have hreal : Summable fun u : ℕ => ‖q‖ ^ u.choose 2 / finiteQPochhammerIn ‖q‖ ‖q‖ u * ‖w‖ ^ u := by
    refine (hasSum_euler_product hq' (-‖w‖)).summable.congr fun u => ?_
    have hsign : (-1 : ℝ) ^ u * (-‖w‖) ^ u = ‖w‖ ^ u := by
      rw [← mul_pow, neg_one_mul, neg_neg]
    rw [show (-1 : ℝ) ^ u * ‖q‖ ^ u.choose 2 / finiteQPochhammerIn ‖q‖ ‖q‖ u * (-‖w‖) ^ u =
        ‖q‖ ^ u.choose 2 / finiteQPochhammerIn ‖q‖ ‖q‖ u * ((-1) ^ u * (-‖w‖) ^ u) by ring, hsign]
  refine Summable.of_nonneg_of_le (fun u => norm_nonneg _) (fun u => ?_)
    (hreal.mul_left (qPochhammerInfIn ‖q‖ ‖q‖)⁻¹)
  have hfin : qPochhammerInfIn ‖q‖ ‖q‖ ≤ ‖finiteQPochhammerIn q q u‖ :=
    qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn q hq1.le hq u
  have hfu0 : 0 < finiteQPochhammerIn ‖q‖ ‖q‖ u :=
    finiteQPochhammerIn_self_pos (norm_nonneg q) hq1 u
  have hfu1 : finiteQPochhammerIn ‖q‖ ‖q‖ u ≤ 1 := by
    have := finiteQPochhammerIn_pow_le_one (norm_nonneg q) hq1.le 1 u
    rwa [pow_one] at this
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_pow]
  calc ‖q‖ ^ u.choose 2 / ‖finiteQPochhammerIn q q u‖ * ‖w‖ ^ u
      ≤ ‖q‖ ^ u.choose 2 / qPochhammerInfIn ‖q‖ ‖q‖ * ‖w‖ ^ u := by
        gcongr
    _ = (qPochhammerInfIn ‖q‖ ‖q‖)⁻¹ * (‖q‖ ^ u.choose 2 * ‖w‖ ^ u) := by ring
    _ ≤ (qPochhammerInfIn ‖q‖ ‖q‖)⁻¹ *
          (‖q‖ ^ u.choose 2 / finiteQPochhammerIn ‖q‖ ‖q‖ u * ‖w‖ ^ u) := by
        gcongr
        exact le_div_self (by positivity) hfu0 hfu1

omit [CompleteSpace 𝕜] in
/-- The terms of Euler's reciprocal expansion are norm-summable for `‖w‖ < 1`. -/
theorem summable_norm_euler_reciprocal_term {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜} (hw : ‖w‖ < 1) :
    Summable fun v : ℕ => ‖w ^ v / finiteQPochhammerIn q q v‖ := by
  have hq1 : ‖q‖ < 1 := hq
  have hP : 0 < qPochhammerInfIn ‖q‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg q) hq1 (norm_nonneg q) hq1
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_right (qPochhammerInfIn ‖q‖ ‖q‖)⁻¹)
  have hfin : qPochhammerInfIn ‖q‖ ‖q‖ ≤ ‖finiteQPochhammerIn q q v‖ :=
    qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn q hq1.le hq v
  rw [norm_div, norm_pow, div_eq_mul_inv]
  gcongr

/-- **The ratio expansion**: for `‖q‖ < 1` and `‖b_j z‖ < 1` for all `j`,
`∏_i (a_i z;q)_∞ / ∏_j (b_j z;q)_∞ = ∑_N c_N z^N` with
`c_N = ∑_{u_1+⋯+u_r+v_1+⋯+v_s=N} ∏_i (-1)^{u_i} q^{C(u_i,2)} a_i^{u_i}/(q;q)_{u_i}
∏_j b_j^{v_j}/(q;q)_{v_j}`; the two coefficient families are concatenated by `Fin.append`. -/
theorem hasSum_ratio_expansion {q : 𝕜} (hq : ‖q‖ < 1) {r s : ℕ} (a : Fin r → 𝕜) (b : Fin s → 𝕜)
    {z : 𝕜} (hb : ∀ j, ‖b j * z‖ < 1) :
    HasSum (fun N : ℕ => (∑ i ∈ Finset.Nat.antidiagonalTuple (r + s) N, ∏ k,
        Fin.append (fun i u => (-1 : 𝕜) ^ u * q ^ u.choose 2 / finiteQPochhammerIn q q u * a i ^ u)
          (fun j v => b j ^ v / finiteQPochhammerIn q q v) k (i k)) * z ^ N)
      ((∏ i, qPochhammerInfIn (a i * z) q) / ∏ j, qPochhammerInfIn (b j * z) q) := by
  set c : Fin (r + s) → ℕ → 𝕜 :=
    Fin.append (fun i u => (-1 : 𝕜) ^ u * q ^ u.choose 2 / finiteQPochhammerIn q q u * a i ^ u)
      (fun j v => b j ^ v / finiteQPochhammerIn q q v) with hc
  have hsum : ∀ k, Summable fun n => ‖c k n * z ^ n‖ := by
    intro k
    induction k using Fin.addCases with
    | left i =>
      simp only [hc, Fin.append_left]
      refine (summable_norm_euler_product_term hq (a i * z)).congr fun n => ?_
      rw [mul_pow, mul_assoc]
    | right j =>
      simp only [hc, Fin.append_right]
      refine (summable_norm_euler_reciprocal_term hq (hb j)).congr fun n => ?_
      rw [mul_pow, div_mul_eq_mul_div]
  have h := hasSum_prod_powerSeries c z hsum
  rw [Fin.prod_univ_add] at h
  have hL : ∀ i : Fin r, ∑' n, c (Fin.castAdd s i) n * z ^ n = qPochhammerInfIn (a i * z) q :=
    fun i => by
      simp only [hc, Fin.append_left]
      refine ((hasSum_euler_product hq (a i * z)).congr_fun fun n => ?_).tsum_eq
      rw [mul_pow, mul_assoc]
  have hR : ∀ j : Fin s, ∑' n, c (Fin.natAdd r j) n * z ^ n =
      (qPochhammerInfIn (b j * z) q)⁻¹ := fun j => by
    simp only [hc, Fin.append_right]
    refine ((hasSum_euler_reciprocal hq (hb j)).congr_fun fun n => ?_).tsum_eq
    rw [mul_pow, div_mul_eq_mul_div]
  simp only [hL, hR] at h
  rw [prod_inv_distrib, ← div_eq_mul_inv] at h
  exact h

end Fabius
