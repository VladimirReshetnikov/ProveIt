import FabiusFunction.AndrewsGordonOne
import FabiusFunction.PartitionGeneratingFunction
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Andrews–Gordon with free summation indices

The Andrews–Gordon identities (qg:thm-andrews-gordon) are stated in the monograph over
*independent* indices `n_1, …, n_{k-1} ≥ 0`, with `N_j = n_j + ⋯ + n_{k-1}`:

  `∑_{n_1,…,n_{K}} q^{N_1²+⋯+N_K²+N_i+⋯+N_K} / ((q;q)_{n_1} ⋯ (q;q)_{n_K})
     = (q^i, q^{M-i}, q^M; q^M)_∞ / (q;q)_∞`,   `K = k-1`, `M = 2k+1`.

The Bailey-chain proof produces instead the *decreasing* form
(qg:eq:andrews-gordon-decreasing), a sum over `r_1 ≥ ⋯ ≥ r_K ≥ 0` with `r_j = N_j`.  In the
corpus that form is `hasSum_andrewsGordon_one` (the case `i = 1`) and
`hasSum_andrewsGordon_of_two_le` (the cases `2 ≤ i ≤ k`, with `t = k-i+1`, `u = i-2`): the outer
`HasSum` index is `r_1` and the nested `Finset` sums inside `baileyChainBeta` carry `r_2, …, r_K`.

The passage from the decreasing form to the free form is the substitution `n_j = r_j - r_{j+1}`,
which the monograph asserts in a single sentence and does not justify.  This module proves it.

## Main declarations

*Reindexing (one chain variable at a time).*

* `hasSum_sum_antidiagonal`: a convergent family on `ℕ × ℕ` may be summed along antidiagonals.
* `hasSum_of_hasSum_sum_range`: conversely, if `G : ℕ × ℕ → 𝕜` is summable and the antidiagonal
  sums `∑_{j ≤ n} G (j, n - j)` have sum `S`, then `HasSum G S`.  This *is* the bijection
  `{(n, j) : j ≤ n} ≃ ℕ × ℕ`, `(n, j) ↦ (j, n - j)`, i.e. exactly one step `n_j = r_j - r_{j+1}`.
* `hasSum_of_hasSum_sum_range'`: the mirrored orientation `(n, j) ↦ (n - j, j)`, with the
  constrained sums `∑_{j ≤ n} G (n - j, j)`.  This is the orientation a Bailey chain produces:
  `j = r_{j+1}` is the inner index and `n - j = n_j` is the freed difference.
* `hasSum_pair_of_hasSum_baileyChain_one`: the Bailey-chain form of one step, for an arbitrary
  weight `W`, arbitrary `β` and arbitrary `a`.  This is the induction step that a treatment of
  general `K` would iterate.

*The modulus-seven family (qg:cor-andrews-gordon-mod7), in free-index form.*

* `agFreeTermTwo q e₁ e₂ (r, s) = q^{N_1²+N_2²+e₁N_1+e₂N_2} / ((q;q)_r (q;q)_s)` with
  `N_1 = r + s`, `N_2 = s`: the summand of the corollary, with `(e₁, e₂) = (1,1), (0,1), (0,0)`
  for `i = 1, 2, 3`.
* `summable_agFreeTermTwo`: absolute convergence for `‖q‖ < 1`, by the majorant
  `C² ‖q‖^{r²} ‖q‖^{s²}` with `C` the uniform bound `‖(q;q)_m‖⁻¹ ≤ C` of
  `inv_norm_finiteQPochhammerIn_le`.  This is the monograph's convergence paragraph, made into
  the hypothesis that actually licenses the change of index set.
* `hasSum_agFreeTermTwo_of_nested`: the reindexing, specialised to `K = 2`.
* `qPochhammerInfIn_self_dissection_seven`: `(q;q)_∞ = ∏_{s=1}^{7} (q^s; q^7)_∞`.
* `hasSum_andrewsGordon_free_mod_seven_one`, `_two`, `_three`: the three identities
  (qg:eq:andrews-gordon-mod-seven-one)–(three), verbatim, with the right sides in the fully
  reduced products `1/(q²,q³,q⁴,q⁵;q⁷)_∞`, `1/(q,q³,q⁴,q⁶;q⁷)_∞`, `1/(q,q²,q⁵,q⁶;q⁷)_∞`.

## Scope

Everything holds for `‖q‖ < 1` in an arbitrary complete normed field, not just over `ℂ` as in
the monograph.  The three modulus-seven statements are unconditional: there are no `k`, `i`
side conditions left to discharge.

Not covered here: the free-index form of qg:thm-andrews-gordon for general `K = k-1 ≥ 3`.
Iterating `hasSum_pair_of_hasSum_baileyChain_one` requires an induction over a family of shifted
weights, a summable majorant for `Fin K → ℕ`-indexed families, and the reassociation
`(Fin (t+1) → ℕ) × ℕ ≃ ℕ × ((Fin t → ℕ) × ℕ)`; that belongs in a follow-up module.  The case
`K = 1` (`k = 2`, Rogers–Ramanujan, modulus five) needs no reindexing at all — the decreasing
form already has a single variable — and is `hasSum_rogersRamanujan_first` and
`hasSum_rogersRamanujan_second`.  The combinatorial reading of the corollary ("the coefficient
of `q^n` counts partitions of `n` into parts not congruent to `0` or `±i` mod `7`") is a
separate partition-generating-function statement and is not formalised here.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

section Reindexing

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Summation along antidiagonals.**  A convergent family on `ℕ × ℕ` may be summed by
grouping the pairs `(a, b)` with `a + b = n`. -/
theorem hasSum_sum_antidiagonal {G : ℕ × ℕ → 𝕜} {S : 𝕜} (hG : HasSum G S) :
    HasSum (fun n : ℕ => ∑ p ∈ Finset.antidiagonal n, G p) S :=
  hasSum_regroup hG (fun p => p.1 + p.2) Finset.antidiagonal fun _ _ => Finset.mem_antidiagonal

/-- **The reindexing `n_j = r_j - r_{j+1}`, one step.**  If `G : ℕ × ℕ → 𝕜` is absolutely
summable and the constrained sums `∑_{j ≤ n} G (j, n - j)` add up to `S`, then the free double
series `∑_{(a,b)} G (a, b)` also converges to `S`.  The pair `(j, n - j)` runs over the
antidiagonal, so this is the bijection `{(n, j) : j ≤ n} ≃ ℕ × ℕ`. -/
theorem hasSum_of_hasSum_sum_range {G : ℕ × ℕ → 𝕜} {S : 𝕜} (hG : Summable G)
    (h : HasSum (fun n : ℕ => ∑ j ∈ range (n + 1), G (j, n - j)) S) : HasSum G S := by
  have hstep : HasSum (fun n : ℕ => ∑ j ∈ range (n + 1), G (j, n - j)) (∑' p, G p) := by
    refine (hasSum_sum_antidiagonal hG.hasSum).congr_fun fun n => ?_
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk G n).symm
  rw [h.unique hstep]
  exact hG.hasSum

/-- The mirrored orientation of `hasSum_of_hasSum_sum_range`: the inner index is the second
coordinate.  This is the orientation a Bailey chain produces, where `j = r_{j+1}` is the inner
summation variable and `n - j = n_j` is the freed difference. -/
theorem hasSum_of_hasSum_sum_range' {G : ℕ × ℕ → 𝕜} {S : 𝕜} (hG : Summable G)
    (h : HasSum (fun n : ℕ => ∑ j ∈ range (n + 1), G (n - j, j)) S) : HasSum G S := by
  refine hasSum_of_hasSum_sum_range hG (h.congr_fun fun n => ?_)
  rw [← Finset.sum_range_reflect (fun j => G (j, n - j)) (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 : n + 1 - 1 - j = n - j := by omega
  show G (n + 1 - 1 - j, n - (n + 1 - 1 - j)) = G (n - j, j)
  rw [h1, Nat.sub_sub_self hjn]

/-- **One Bailey-chain step in free-index form.**  For an arbitrary weight `W`, an arbitrary
sequence `β` and an arbitrary parameter `a`, the weighted single chain step
`∑_n W n · β^{(1)}_n` equals the free double series
`∑_{(r,d)} W (r+d) · a^r q^{r²} β_r / (q;q)_d`, provided the latter converges absolutely.
Here `r = j` is the inner chain variable — the surviving decreasing index — and `d = n - j` is
the freed difference; the outer index `n = r + d` is what the reindexing eliminates. -/
theorem hasSum_pair_of_hasSum_baileyChain_one {a q : 𝕜} {β W : ℕ → 𝕜} {S : 𝕜}
    (hsum : Summable fun p : ℕ × ℕ =>
      W (p.1 + p.2) * (a ^ p.1 * q ^ (p.1 * p.1) / finiteQPochhammerIn q q p.2 * β p.1))
    (h : HasSum (fun n : ℕ => W n * baileyChainBeta a q β 1 n) S) :
    HasSum (fun p : ℕ × ℕ =>
      W (p.1 + p.2) * (a ^ p.1 * q ^ (p.1 * p.1) / finiteQPochhammerIn q q p.2 * β p.1)) S := by
  refine hasSum_of_hasSum_sum_range hsum (h.congr_fun fun n => ?_)
  have hb : baileyChainBeta a q β 1 n = ∑ j ∈ range (n + 1),
      a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * β j :=
    baileyChainBeta_succ a q β 0 n
  rw [hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  show W (j + (n - j)) * (a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * β j) =
    W n * (a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * β j)
  rw [Nat.add_sub_cancel' hjn]

end Reindexing

section FreeTerm

variable {K : Type*} [Field K]

/-- The summand of the modulus-seven Andrews–Gordon identities with free indices:
with `p = (r, s)`, `N₁ = r + s` and `N₂ = s`,

  `agFreeTermTwo q e₁ e₂ (r, s) = q^{N₁² + N₂² + e₁N₁ + e₂N₂} / ((q;q)_r (q;q)_s)`.

The three cases `i = 1, 2, 3` of qg:cor-andrews-gordon-mod7 are `(e₁, e₂) = (1,1)`, `(0,1)`,
`(0,0)`: `e₁ = 1` exactly when `i ≤ 1` and `e₂ = 1` exactly when `i ≤ 2`. -/
def agFreeTermTwo (q : K) (e₁ e₂ : ℕ) (p : ℕ × ℕ) : K :=
  q ^ ((p.1 + p.2) * (p.1 + p.2) + e₁ * (p.1 + p.2) + (p.2 * p.2 + e₂ * p.2)) /
    (finiteQPochhammerIn q q p.1 * finiteQPochhammerIn q q p.2)

/-- `agFreeTermTwo` evaluated at an explicit pair. -/
theorem agFreeTermTwo_apply (q : K) (e₁ e₂ r s : ℕ) :
    agFreeTermTwo q e₁ e₂ (r, s) =
      q ^ ((r + s) * (r + s) + e₁ * (r + s) + (s * s + e₂ * s)) /
        (finiteQPochhammerIn q q r * finiteQPochhammerIn q q s) := rfl

end FreeTerm

section ModSeven

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- Absolute convergence of the free-index modulus-seven series.  The exponent
`N₁² + N₂² + e₁N₁ + e₂N₂` dominates `r² + s²`, and `‖(q;q)_m‖⁻¹` is bounded uniformly in `m`;
this is the monograph's majorant `C_{R,K} (∑_n R^{n²})^K` for `K = 2`. -/
theorem summable_agFreeTermTwo {q : 𝕜} (hq : ‖q‖ < 1) (e₁ e₂ : ℕ) :
    Summable (agFreeTermTwo q e₁ e₂) := by
  have hQ : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  obtain ⟨C, hC0, hCle⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖finiteQPochhammerIn q q n‖⁻¹ ≤ C := by
    refine ⟨qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖, ?_,
      fun n => inv_norm_finiteQPochhammerIn_le q hq hQ n⟩
    exact (inv_nonneg.mpr (norm_nonneg _)).trans (inv_norm_finiteQPochhammerIn_le q hq hQ 0)
  have hsq : Summable fun n : ℕ => ‖q ^ (n * n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg q) hq)
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_mul_self n)
  have hmul : Summable fun p : ℕ × ℕ => ‖q ^ (p.1 * p.1) * q ^ (p.2 * p.2)‖ :=
    Summable.mul_norm (f := fun n : ℕ => q ^ (n * n)) (g := fun n : ℕ => q ^ (n * n)) hsq hsq
  have hmaj : Summable fun p : ℕ × ℕ => C * C * ‖q ^ (p.1 * p.1) * q ^ (p.2 * p.2)‖ :=
    hmul.mul_left (C * C)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hmaj)
  have hE : p.1 * p.1 + p.2 * p.2 ≤
      (p.1 + p.2) * (p.1 + p.2) + e₁ * (p.1 + p.2) + (p.2 * p.2 + e₂ * p.2) :=
    calc p.1 * p.1 + p.2 * p.2 ≤ (p.1 + p.2) * (p.1 + p.2) + p.2 * p.2 :=
          Nat.add_le_add_right
            (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)) _
      _ ≤ (p.1 + p.2) * (p.1 + p.2) + e₁ * (p.1 + p.2) + (p.2 * p.2 + e₂ * p.2) :=
          Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hnorm : ‖agFreeTermTwo q e₁ e₂ p‖ =
      ‖q‖ ^ ((p.1 + p.2) * (p.1 + p.2) + e₁ * (p.1 + p.2) + (p.2 * p.2 + e₂ * p.2)) *
        (‖finiteQPochhammerIn q q p.1‖⁻¹ * ‖finiteQPochhammerIn q q p.2‖⁻¹) := by
    simp only [agFreeTermTwo, norm_div, norm_pow, norm_mul]
    rw [div_eq_mul_inv, mul_inv]
  have hmajn : ‖q ^ (p.1 * p.1) * q ^ (p.2 * p.2)‖ = ‖q‖ ^ (p.1 * p.1) * ‖q‖ ^ (p.2 * p.2) := by
    rw [norm_mul, norm_pow, norm_pow]
  rw [hnorm, hmajn]
  have h1 : ‖q‖ ^ ((p.1 + p.2) * (p.1 + p.2) + e₁ * (p.1 + p.2) + (p.2 * p.2 + e₂ * p.2)) ≤
      ‖q‖ ^ (p.1 * p.1) * ‖q‖ ^ (p.2 * p.2) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (norm_nonneg q) hq.le hE
  have h2 : ‖finiteQPochhammerIn q q p.1‖⁻¹ * ‖finiteQPochhammerIn q q p.2‖⁻¹ ≤ C * C :=
    mul_le_mul (hCle _) (hCle _) (inv_nonneg.mpr (norm_nonneg _)) hC0
  have h3 : (0 : ℝ) ≤ ‖finiteQPochhammerIn q q p.1‖⁻¹ * ‖finiteQPochhammerIn q q p.2‖⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _))
  have h4 : (0 : ℝ) ≤ ‖q‖ ^ (p.1 * p.1) * ‖q‖ ^ (p.2 * p.2) :=
    mul_nonneg (pow_nonneg (norm_nonneg q) _) (pow_nonneg (norm_nonneg q) _)
  exact le_trans (mul_le_mul h1 h2 h3 h4) (le_of_eq (mul_comm _ _))

/-- **The reindexing for `K = 2`.**  The decreasing form of the modulus-seven Andrews–Gordon
sums — outer index `n = N₁`, inner index `j = N₂` — has the same sum as the free-index form,
with `r = n - j` and `s = j`. -/
theorem hasSum_agFreeTermTwo_of_nested {q : 𝕜} (hq : ‖q‖ < 1) (e₁ e₂ : ℕ) {S : 𝕜}
    (h : HasSum (fun n : ℕ => ∑ j ∈ range (n + 1),
        q ^ (n * n + e₁ * n + (j * j + e₂ * j)) /
          (finiteQPochhammerIn q q (n - j) * finiteQPochhammerIn q q j)) S) :
    HasSum (agFreeTermTwo q e₁ e₂) S := by
  refine hasSum_of_hasSum_sum_range' (summable_agFreeTermTwo hq e₁ e₂) (h.congr_fun fun n => ?_)
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [agFreeTermTwo_apply, Nat.sub_add_cancel hjn]

/-! ### The sevenfold dissection -/

omit [CompleteSpace 𝕜] in
/-- `‖q⁷‖ < 1` whenever `‖q‖ < 1`. -/
theorem norm_pow_seven_lt_one {q : 𝕜} (hq : ‖q‖ < 1) : ‖q ^ 7‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)

/-- The factors `(q^k; q^7)_∞` of the sevenfold dissection are nonzero for `1 ≤ k`. -/
theorem qPochhammerInfIn_pow_pow_seven_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {k : ℕ} (hk : 1 ≤ k) :
    qPochhammerInfIn (q ^ k) (q ^ 7) ≠ 0 :=
  qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_seven_lt_one hq)
    (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega))

/-- The sevenfold dissection
`(q;q)_∞ = (q;q⁷)_∞ (q²;q⁷)_∞ (q³;q⁷)_∞ (q⁴;q⁷)_∞ (q⁵;q⁷)_∞ (q⁶;q⁷)_∞ (q⁷;q⁷)_∞`. -/
theorem qPochhammerInfIn_self_dissection_seven {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q = qPochhammerInfIn q (q ^ 7) * qPochhammerInfIn (q ^ 2) (q ^ 7) *
      qPochhammerInfIn (q ^ 3) (q ^ 7) * qPochhammerInfIn (q ^ 4) (q ^ 7) *
      qPochhammerInfIn (q ^ 5) (q ^ 7) * qPochhammerInfIn (q ^ 6) (q ^ 7) *
      qPochhammerInfIn (q ^ 7) (q ^ 7) := by
  have h := qPochhammerInfIn_dissection q hq (r := 7) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  rw [h, show q * q ^ 0 = q by ring, show q * q ^ 1 = q ^ 2 by ring,
    show q * q ^ 2 = q ^ 3 by ring, show q * q ^ 3 = q ^ 4 by ring,
    show q * q ^ 4 = q ^ 5 by ring, show q * q ^ 5 = q ^ 6 by ring,
    show q * q ^ 6 = q ^ 7 by ring]

/-! ### Cancelling the dissection against the three numerators

These are pure field identities: the sevenfold dissection has seven factors, of which the
numerator of the Andrews–Gordon right side supplies three, and the remaining four survive. -/

section Cancellation

variable {K : Type*} [Field K]

/-- Cancellation for `i = 1`: the numerator classes are `a, f, g`. -/
private theorem prod_div_prod_seven_one {a b c d e f g : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) :
    a * f * g / (a * b * c * d * e * f * g) = (b * c * d * e)⁻¹ := by
  have hD : a * b * c * d * e * f * g ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd)
      he) hf) hg
  have hE : b * c * d * e ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hd) he
  rw [inv_eq_one_div, div_eq_div_iff hD hE]
  ring

/-- Cancellation for `i = 2`: the numerator classes are `b, e, g`. -/
private theorem prod_div_prod_seven_two {a b c d e f g : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) :
    b * e * g / (a * b * c * d * e * f * g) = (a * c * d * f)⁻¹ := by
  have hD : a * b * c * d * e * f * g ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd)
      he) hf) hg
  have hE : a * c * d * f ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero ha hc) hd) hf
  rw [inv_eq_one_div, div_eq_div_iff hD hE]
  ring

/-- Cancellation for `i = 3`: the numerator classes are `c, d, g`. -/
private theorem prod_div_prod_seven_three {a b c d e f g : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) :
    c * d * g / (a * b * c * d * e * f * g) = (a * b * e * f)⁻¹ := by
  have hD : a * b * c * d * e * f * g ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd)
      he) hf) hg
  have hE : a * b * e * f ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) he) hf
  rw [inv_eq_one_div, div_eq_div_iff hD hE]
  ring

end Cancellation

/-! ### The three modulus-seven identities in free-index form -/

/-- **qg:eq:andrews-gordon-mod-seven-one.**  With `N₁ = r + s` and `N₂ = s`,

  `∑_{r,s ≥ 0} q^{N₁² + N₂² + N₁ + N₂} / ((q;q)_r (q;q)_s) = 1/(q², q³, q⁴, q⁵; q⁷)_∞`

for `‖q‖ < 1`.  This is `k = 3`, `i = 1` of qg:thm-andrews-gordon: two chain steps relative to
`q` applied to the unit pair, with outer weight `q^{n²+n}`. -/
theorem hasSum_andrewsGordon_free_mod_seven_one {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (agFreeTermTwo q 1 1)
      ((qPochhammerInfIn (q ^ 2) (q ^ 7) * qPochhammerInfIn (q ^ 3) (q ^ 7) *
        qPochhammerInfIn (q ^ 4) (q ^ 7) * qPochhammerInfIn (q ^ 5) (q ^ 7))⁻¹) := by
  have h := hasSum_andrewsGordon_one hq 2
  have hval : qPochhammerInfIn q (q ^ 7) * qPochhammerInfIn (q ^ 6) (q ^ 7) *
      qPochhammerInfIn (q ^ 7) (q ^ 7) / qPochhammerInfIn q q =
      (qPochhammerInfIn (q ^ 2) (q ^ 7) * qPochhammerInfIn (q ^ 3) (q ^ 7) *
        qPochhammerInfIn (q ^ 4) (q ^ 7) * qPochhammerInfIn (q ^ 5) (q ^ 7))⁻¹ := by
    rw [qPochhammerInfIn_self_dissection_seven hq]
    exact prod_div_prod_seven_one
      (qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_seven_lt_one hq) hq)
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 2) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 3) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 4) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 5) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 6) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 7) (by norm_num))
  refine hasSum_agFreeTermTwo_of_nested hq 1 1 ?_
  rw [← hval]
  refine h.congr_fun fun n => ?_
  have hb : baileyChainBeta q q unitBaileyBeta 2 n = ∑ j ∈ range (n + 1),
      q ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
        baileyChainBeta q q unitBaileyBeta 1 j :=
    baileyChainBeta_succ q q unitBaileyBeta 1 n
  rw [hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [baileyChainBeta_unit_one]
  have hpow : q ^ (n * n + 1 * n + (j * j + 1 * j)) =
      q ^ (n * (n + 1)) * (q ^ j * q ^ (j * j)) := by
    rw [show n * n + 1 * n + (j * j + 1 * j) = n * (n + 1) + (j + j * j) by ring, pow_add, pow_add]
  rw [hpow]
  ring

/-- **qg:eq:andrews-gordon-mod-seven-two.**  With `N₁ = r + s` and `N₂ = s`,

  `∑_{r,s ≥ 0} q^{N₁² + N₂² + N₂} / ((q;q)_r (q;q)_s) = 1/(q, q³, q⁴, q⁶; q⁷)_∞`

for `‖q‖ < 1`.  This is `k = 3`, `i = 2`, i.e. `t = 2` chain steps relative to `q`, the
lowering shift, and `u = 0` steps relative to `1`, with outer weight `q^{n²}`. -/
theorem hasSum_andrewsGordon_free_mod_seven_two {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (agFreeTermTwo q 0 1)
      ((qPochhammerInfIn q (q ^ 7) * qPochhammerInfIn (q ^ 3) (q ^ 7) *
        qPochhammerInfIn (q ^ 4) (q ^ 7) * qPochhammerInfIn (q ^ 6) (q ^ 7))⁻¹) := by
  have h := hasSum_andrewsGordon_of_two_le hq 2 0
  have hval : qPochhammerInfIn (q ^ 2) (q ^ 7) * qPochhammerInfIn (q ^ 5) (q ^ 7) *
      qPochhammerInfIn (q ^ 7) (q ^ 7) / qPochhammerInfIn q q =
      (qPochhammerInfIn q (q ^ 7) * qPochhammerInfIn (q ^ 3) (q ^ 7) *
        qPochhammerInfIn (q ^ 4) (q ^ 7) * qPochhammerInfIn (q ^ 6) (q ^ 7))⁻¹ := by
    rw [qPochhammerInfIn_self_dissection_seven hq]
    exact prod_div_prod_seven_two
      (qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_seven_lt_one hq) hq)
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 2) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 3) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 4) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 5) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 6) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 7) (by norm_num))
  refine hasSum_agFreeTermTwo_of_nested hq 0 1 ?_
  rw [← hval]
  refine h.congr_fun fun n => ?_
  have hb : baileyChainBeta q q unitBaileyBeta 2 n = ∑ j ∈ range (n + 1),
      q ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
        baileyChainBeta q q unitBaileyBeta 1 j :=
    baileyChainBeta_succ q q unitBaileyBeta 1 n
  rw [baileyChainBeta_zero, hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [baileyChainBeta_unit_one]
  have hpow : q ^ (n * n + 0 * n + (j * j + 1 * j)) =
      q ^ (n * n) * (q ^ j * q ^ (j * j)) := by
    rw [show n * n + 0 * n + (j * j + 1 * j) = n * n + (j + j * j) by ring, pow_add, pow_add]
  rw [hpow]
  ring

/-- **qg:eq:andrews-gordon-mod-seven-three.**  With `N₁ = r + s` and `N₂ = s`,

  `∑_{r,s ≥ 0} q^{N₁² + N₂²} / ((q;q)_r (q;q)_s) = 1/(q, q², q⁵, q⁶; q⁷)_∞`

for `‖q‖ < 1`.  This is `k = 3`, `i = 3`, i.e. `t = 1` chain step relative to `q`, the lowering
shift, and `u = 1` step relative to `1`, with outer weight `q^{n²}`. -/
theorem hasSum_andrewsGordon_free_mod_seven_three {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (agFreeTermTwo q 0 0)
      ((qPochhammerInfIn q (q ^ 7) * qPochhammerInfIn (q ^ 2) (q ^ 7) *
        qPochhammerInfIn (q ^ 5) (q ^ 7) * qPochhammerInfIn (q ^ 6) (q ^ 7))⁻¹) := by
  have h := hasSum_andrewsGordon_of_two_le hq 1 1
  have hval : qPochhammerInfIn (q ^ 3) (q ^ 7) * qPochhammerInfIn (q ^ 4) (q ^ 7) *
      qPochhammerInfIn (q ^ 7) (q ^ 7) / qPochhammerInfIn q q =
      (qPochhammerInfIn q (q ^ 7) * qPochhammerInfIn (q ^ 2) (q ^ 7) *
        qPochhammerInfIn (q ^ 5) (q ^ 7) * qPochhammerInfIn (q ^ 6) (q ^ 7))⁻¹ := by
    rw [qPochhammerInfIn_self_dissection_seven hq]
    exact prod_div_prod_seven_three
      (qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_seven_lt_one hq) hq)
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 2) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 3) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 4) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 5) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 6) (by norm_num))
      (qPochhammerInfIn_pow_pow_seven_ne_zero hq (k := 7) (by norm_num))
  refine hasSum_agFreeTermTwo_of_nested hq 0 0 ?_
  rw [← hval]
  refine h.congr_fun fun n => ?_
  have hb : baileyChainBeta (1 : 𝕜) q (baileyChainBeta q q unitBaileyBeta 1) 1 n =
      ∑ j ∈ range (n + 1), (1 : 𝕜) ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
        baileyChainBeta q q unitBaileyBeta 1 j :=
    baileyChainBeta_succ 1 q (baileyChainBeta q q unitBaileyBeta 1) 0 n
  rw [hb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [baileyChainBeta_unit_one, one_pow]
  have hpow : q ^ (n * n + 0 * n + (j * j + 0 * j)) = q ^ (n * n) * q ^ (j * j) := by
    rw [show n * n + 0 * n + (j * j + 0 * j) = n * n + j * j by ring, pow_add]
  rw [hpow]
  ring

end ModSeven

end Fabius
