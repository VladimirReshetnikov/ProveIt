import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of absolutely convergent series and the geometric simplex sum

For norm-summable `g k : ℕ → 𝕜` (`k : Fin ℓ`),

`∑_{i : Fin ℓ → ℕ} ∏_k g k (i k) = ∏_k ∑_n g k n`

absolutely (`hasSum_prod_fin_pi`), by induction on `ℓ` through `Fin.consEquiv` and the Cauchy
product of two absolutely convergent series.

Specializing to geometric series gives the **geometric simplex sum** of the monograph in its
increment parametrization: writing a strictly increasing sequence `1 ≤ j_1 < ⋯ < j_ℓ` as
`j_h = ∑_{k ≤ h} (i_k + 1)` with `i : Fin ℓ → ℕ` (written with `if k ≤ h` inside the sums),
and `t_h = r_h + ⋯ + r_ℓ`,

`∑_{i} q^{∑_h j_h r_h} = ∏_h q^{t_h}/(1 - q^{t_h})`   (`‖q‖ < 1`, all `r_h ≥ 1`),

because `∑_h j_h r_h = ∑_k (i_k + 1) t_k` (`sum_prefix_mul_eq_sum_mul_tailSum`).

## Main declarations

* `hasSum_prod_fin_pi`.
* `tailSum`, `tailSum_pos`, `sum_prefix_mul_eq_sum_mul_tailSum`.
* `hasSum_geometric_simplex_increments`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

set_option maxHeartbeats 400000 in
/-- **Products of absolutely convergent series over a finite index set**: if every `g k` is
norm-summable, then `∑_{i : Fin ℓ → ℕ} ∏_k g k (i k) = ∏_k ∑_n g k n`, and the product terms are
norm-summable. -/
theorem hasSum_prod_fin_pi : ∀ (ℓ : ℕ) (g : Fin ℓ → ℕ → 𝕜),
    (∀ k, Summable fun n => ‖g k n‖) →
      HasSum (fun i : Fin ℓ → ℕ => ∏ k, g k (i k)) (∏ k, ∑' n, g k n) ∧
        Summable fun i : Fin ℓ → ℕ => ‖∏ k, g k (i k)‖ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro g _
    simp only [Finset.univ_eq_empty, prod_empty, norm_one]
    exact ⟨by simpa using hasSum_fintype (fun _ : Fin 0 → ℕ => (1 : 𝕜)),
      (hasSum_fintype _).summable⟩
  | succ ℓ ih =>
    intro g hg
    obtain ⟨ih1, ih2⟩ := ih (fun k => g k.succ) fun k => hg k.succ
    let e := Fin.consEquiv (fun _ : Fin (ℓ + 1) => ℕ)
    have key : ∀ p : ℕ × (Fin ℓ → ℕ),
        (∏ k, g k (e p k)) = g 0 p.1 * ∏ k : Fin ℓ, g k.succ (p.2 k) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    have hf0 : HasSum (g 0) (∑' n, g 0 n) := (hg 0).of_norm.hasSum
    have hmul := summable_mul_of_summable_norm (f := g 0)
      (g := fun i : Fin ℓ → ℕ => ∏ k : Fin ℓ, g k.succ (i k)) (hg 0) ih2
    have hprod := HasSum.mul (f := g 0) (g := fun i : Fin ℓ → ℕ => ∏ k : Fin ℓ, g k.succ (i k))
      hf0 ih1 hmul
    have hnorm : Summable fun p : ℕ × (Fin ℓ → ℕ) =>
        ‖g 0 p.1 * ∏ k : Fin ℓ, g k.succ (p.2 k)‖ := by
      simp only [norm_mul]
      exact summable_mul_of_summable_norm (f := fun n => ‖g 0 n‖)
        (g := fun i : Fin ℓ → ℕ => ‖∏ k : Fin ℓ, g k.succ (i k)‖) (by simpa using hg 0)
        (by simpa using ih2)
    refine ⟨?_, ?_⟩
    · rw [Fin.prod_univ_succ, ← e.hasSum_iff]
      exact hprod.congr_fun fun p => key p
    · rw [← e.summable_iff]
      exact hnorm.congr fun p => by rw [Function.comp_apply, key p]

/-- The tail sums `t_h = ∑_{k ≥ h} r_k`. -/
def tailSum {ℓ : ℕ} (r : Fin ℓ → ℕ) (h : Fin ℓ) : ℕ := ∑ k, if h ≤ k then r k else 0

/-- Every tail sum is positive when each summand is positive. -/
theorem tailSum_pos {ℓ : ℕ} {r : Fin ℓ → ℕ} (hr : ∀ h, 0 < r h) (h : Fin ℓ) :
    0 < tailSum r h := by
  unfold tailSum
  refine lt_of_lt_of_le (hr h) ?_
  have := single_le_sum (s := univ) (f := fun k => if h ≤ k then r k else 0)
    (fun _ _ => by positivity) (mem_univ h)
  simpa using this

/-- The exponent identity behind the simplex sum:
`∑_h (∑_{k ≤ h} (i_k + 1)) r_h = ∑_k (i_k + 1) t_k`. -/
theorem sum_prefix_mul_eq_sum_mul_tailSum {ℓ : ℕ} (r i : Fin ℓ → ℕ) :
    ∑ h, (∑ k, if k ≤ h then i k + 1 else 0) * r h = ∑ k, (i k + 1) * tailSum r k := by
  unfold tailSum
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun h _ => ?_
  by_cases hkh : k ≤ h <;> simp [hkh]

/-- **The geometric simplex sum** (increment parametrization): for `‖q‖ < 1` and positive
`r_1, …, r_ℓ` with tail sums `t_h`, summing `q^{∑_h j_h r_h}` over all strictly increasing
`1 ≤ j_1 < ⋯ < j_ℓ`, written as `j_h = ∑_{k ≤ h} (i_k + 1)`, gives `∏_h q^{t_h}/(1 - q^{t_h})`. -/
theorem hasSum_geometric_simplex_increments {q : 𝕜} (hq : ‖q‖ < 1) {ℓ : ℕ} (r : Fin ℓ → ℕ)
    (hr : ∀ h, 0 < r h) :
    HasSum (fun i : Fin ℓ → ℕ => q ^ (∑ h, (∑ k, if k ≤ h then i k + 1 else 0) * r h))
      (∏ h, q ^ tailSum r h / (1 - q ^ tailSum r h)) := by
  have hlt : ∀ k : Fin ℓ, ‖q ^ tailSum r k‖ < 1 := fun k => by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (tailSum_pos hr k).ne'
  have hg : ∀ k : Fin ℓ, Summable fun n : ℕ => ‖(q ^ tailSum r k) ^ (n + 1)‖ := fun k =>
    (summable_nat_add_iff (f := fun n : ℕ => ‖(q ^ tailSum r k) ^ n‖) 1).mpr
      ((summable_geometric_of_lt_one (norm_nonneg _) (hlt k)).congr fun n => (norm_pow _ _).symm)
  obtain ⟨h, -⟩ := hasSum_prod_fin_pi ℓ (fun k n => (q ^ tailSum r k) ^ (n + 1)) hg
  have hval : ∀ k : Fin ℓ, ∑' n : ℕ, (q ^ tailSum r k) ^ (n + 1) =
      q ^ tailSum r k / (1 - q ^ tailSum r k) := fun k => by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hlt k), div_eq_mul_inv]
  rw [prod_congr rfl fun k _ => hval k] at h
  refine h.congr_fun fun i => ?_
  rw [sum_prefix_mul_eq_sum_mul_tailSum, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun k _ => ?_
  rw [← pow_mul, mul_comm]

end Fabius
