import Surreal.Surcomplex.CosineFold
import Surreal.Surcomplex.StrongReindex
import Surreal.Surcomplex.AcosEndpointSeries

/-!
# The complete strong series of the complex cosine fold

The odd inverse-sine terms regroup into the endpoint series, now for
arbitrary actual complex infinitesimal parameters. The square-root choices
are coherent: `s^2=τ/2` makes `2s` a square root of `2τ`. This proves the
full-series equality in `trigonometry:eq:foldroots` with an exact finite
remainder after the displayed cubic factor.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The odd complex inverse-sine terms form an actual strongly summable family. -/
theorem stronglySummable_infArcsin (s : Surcomplex.{u}) (hs : IsInfinitesimal s) :
    StronglySummable (fun n : ℕ =>
      ofComplex ((Nat.centralBinom n : ℂ) / (4 ^ n * (2 * n + 1))) * s ^ (2 * n + 1)) := by
  have h := stronglySummable_powerSeries s hs Analytic.complexArcsinSeries
  simpa only [Analytic.coeff_complexArcsinSeries_odd] using
    h.comp_injective (fun n : ℕ => 2 * n + 1) (by intro a b he; dsimp at he; omega)

/-- The inverse germ is exactly the displayed central-binomial strong sum. -/
theorem infArcsin_eq_strongSum (s : Surcomplex.{u}) (hs : IsInfinitesimal s) :
    infArcsin s hs = strongSum (fun n : ℕ =>
      ofComplex ((Nat.centralBinom n : ℂ) / (4 ^ n * (2 * n + 1))) * s ^ (2 * n + 1))
      (stronglySummable_infArcsin s hs) := by
  have h := stronglySummable_powerSeries s hs Analytic.complexArcsinSeries
  have hz : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k + 1) →
      ofComplex (Analytic.complexArcsinSeries.coeff n) * s ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [Analytic.coeff_complexArcsinSeries_even, map_zero, zero_mul]
    · exact (hn ⟨k, rfl⟩).elim
  have he := strongSum_comp_injective h (fun n : ℕ => 2 * n + 1)
    (by intro a b hh; dsimp at hh; omega) hz
  rw [infArcsin, powerSeriesEvaluation_eq_strongSum]
  simpa only [Analytic.coeff_complexArcsinSeries_odd] using he.symm

namespace CosineFold

/-- Scalar extension of the already defined real endpoint coefficient series. -/
def endpointSeries : PowerSeries ℂ := acosEndpointSeries.map Complex.ofRealHom

@[simp] theorem coeff_endpointSeries (n : ℕ) : endpointSeries.coeff n =
    (Nat.centralBinom n : ℂ) / (8 ^ n * (2 * n + 1)) := by
  simp only [endpointSeries, PowerSeries.coeff_map, coeff_acosEndpointSeries,
    map_div₀, map_mul, map_pow, map_add, map_natCast, map_ofNat, map_one]

/-- The normalized factor is strongly summable for every complex infinitesimal. -/
theorem stronglySummable_endpoint (τ : Surcomplex.{u}) (hτ : IsInfinitesimal τ) :
    StronglySummable (fun n : ℕ =>
      ofComplex ((Nat.centralBinom n : ℂ) / (8 ^ n * (2 * n + 1))) * τ ^ n) :=
  stronglySummable_coeff_mul_powers τ hτ _

private theorem endpoint_term (τ s : Surcomplex.{u}) (hsq : s ^ 2 = τ / 2) (n : ℕ) :
    2 * (ofComplex ((Nat.centralBinom n : ℂ) / (4 ^ n * (2 * n + 1))) * s ^ (2 * n + 1)) =
      (2 * s) * (ofComplex ((Nat.centralBinom n : ℂ) / (8 ^ n * (2 * n + 1))) * τ ^ n) := by
  rw [pow_succ, pow_mul, hsq, div_pow]
  simp only [map_div₀, map_mul, map_pow, map_add, map_natCast, map_ofNat, map_one]
  have he : (8 : Surcomplex.{u}) ^ n = 4 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The full fold series with a coherent square-root choice, valid also at collision. -/
theorem branch_eq_strongSum (τ s : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hs : IsInfinitesimal s) (hsq : s ^ 2 = τ / 2) :
    branch s hs = (2 * s) * strongSum (fun n : ℕ =>
      ofComplex ((Nat.centralBinom n : ℂ) / (8 ^ n * (2 * n + 1))) * τ ^ n)
      (stronglySummable_endpoint τ hτ) := by
  have h := strongSum_const_mul (stronglySummable_infArcsin s hs) 2
  have he := funext (endpoint_term τ s hsq)
  simp only [he] at h
  rw [branch, infArcsin_eq_strongSum]
  exact h.symm.trans (strongSum_const_mul (stronglySummable_endpoint τ hτ) _)

/-- The strong series factor is admissible formal evaluation of its explicit coefficients. -/
theorem branch_eq_endpoint (τ s : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hs : IsInfinitesimal s) (hsq : s ^ 2 = τ / 2) :
    branch s hs = (2 * s) * powerSeriesEvaluation τ hτ endpointSeries := by
  rw [branch_eq_strongSum τ s hτ hs hsq, powerSeriesEvaluation_eq_strongSum]
  simp only [coeff_endpointSeries]

/-- The displayed expansion has a finite fourth-order tail with known standard part. -/
theorem branch_expansion (τ s : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hs : IsInfinitesimal s) (hsq : s ^ 2 = τ / 2) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = 35 / 18432 ∧
      branch s hs = (2 * s) *
        (1 + τ / 12 + 3 * τ ^ 2 / 160 + 5 * τ ^ 3 / 896 + τ ^ 4 * R) := by
  obtain ⟨R, hR, hr, he⟩ := exists_finite_powerSeries_remainder τ hτ endpointSeries 4
  norm_num [coeff_endpointSeries, Finset.sum_range_succ,
    Nat.centralBinom, Nat.choose_succ_succ, map_div₀, map_ofNat] at hr he
  refine ⟨R, hR, hr, ?_⟩
  rw [branch_eq_endpoint τ s hτ hs hsq, he]
  ring

/-- The scale in the full series is the coherently chosen square root of twice the parameter. -/
theorem scale_sq (τ s : Surcomplex.{u}) (hsq : s ^ 2 = τ / 2) : (2 * s) ^ 2 = 2 * τ := by
  rw [mul_pow, hsq]
  ring

end CosineFold
end
end Surreal.Surcomplex
