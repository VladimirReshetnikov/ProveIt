/-
# Identification with the Bernoulli numbers (Proposition 5.3)

The coefficients `bplus n` of `BCH.Bernoulli` are defined by the recursion of
Proposition 5.3 of the accompanying article (`docs/combined`). This file shows
that they are the coefficients `B⁺ₙ/n!` of the exponential generating function
of the Bernoulli numbers in the convention `B⁺₁ = +1/2` (Mathlib's
`bernoulli'`), as asserted in equation (5.8) of the article:

* `eq_bplus_of_sum_antidiagonal`: the Cauchy identity `∑_{j+k=n} φⱼ cₖ = δ_{n,0}`
  determines the sequence `c` (it is the recursion);
* `bplus_eq_bernoulli'`: `bplus n = bernoulli' n / n!`.

The second statement is obtained from Mathlib's identity
`B(X) (e^X - 1) = X e^X` for `B(X) = ∑ₙ bernoulli' n Xⁿ/n!`: multiplying by
`e^{-X}` gives `B(X) (1 - e^{-X}) = X`, and `1 - e^{-X} = X φ(X)` with
`φ(X) = ∑ⱼ (-1)^j X^j/(j+1)!`, so `B(X) φ(X) = 1`.
-/
import BCH.Bernoulli
import Mathlib.NumberTheory.Bernoulli

open Finset Finset.Nat PowerSeries

namespace BCH

/-- The Cauchy identity `∑_{j+k=n} φⱼ cₖ = δ_{n,0}` determines `c`: it is the recursion
defining `bplus`. -/
theorem eq_bplus_of_sum_antidiagonal {c : ℕ → ℚ}
    (hc : ∀ n, ∑ p ∈ antidiagonal n, phiCoeffQ p.1 * c p.2 = if n = 0 then 1 else 0) :
    ∀ n, c n = bplus n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      have h := hc 0
      simpa using h
    | succ n =>
      have h := hc (n + 1)
      rw [Finset.Nat.sum_antidiagonal_succ, phiCoeffQ_zero, one_mul, if_neg (Nat.succ_ne_zero n),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => phiCoeffQ (i + 1) * c j)] at h
      rw [bplus_succ]
      have : ∑ j ∈ range (n + 1), phiCoeffQ (j + 1) * c (n - j) =
          ∑ j ∈ range (n + 1), phiCoeffQ (j + 1) * bplus (n - j) :=
        sum_congr rfl fun j _ => by rw [ih (n - j) (by omega)]
      linarith [h, this]

/-- **Proposition 5.3, identification**: the recursion-defined coefficients are
`bplus n = B⁺ₙ / n!` with `B⁺ₙ` the Bernoulli numbers in the convention `B⁺₁ = +1/2`. -/
theorem bplus_eq_bernoulli' (n : ℕ) : bplus n = bernoulli' n / n.factorial := by
  set Φ : ℚ⟦X⟧ := PowerSeries.mk phiCoeffQ with hΦ
  set B := bernoulli'PowerSeries ℚ with hB
  set E := PowerSeries.exp ℚ with hE
  set E' := evalNegHom E with hE'
  have hcoeffE' : ∀ k, coeff k E' = (-1) ^ k * (1 / (k.factorial : ℚ)) := by
    intro k
    rw [hE', hE]
    show coeff k (rescale (-1 : ℚ) (PowerSeries.exp ℚ)) = _
    rw [coeff_rescale, coeff_exp]
    simp
  have h3 : X * Φ = 1 - E' := by
    ext k
    cases k with
    | zero =>
      rw [coeff_zero_X_mul, map_sub, coeff_one, hcoeffE' 0]
      simp
    | succ k =>
      rw [coeff_succ_X_mul, map_sub, coeff_one, hcoeffE', if_neg (Nat.succ_ne_zero k), hΦ,
        coeff_mk, phiCoeffQ, pow_succ]
      ring
  have h1 := bernoulli'PowerSeries_mul_exp_sub_one ℚ
  have h2 := exp_mul_exp_neg_eq_one (A := ℚ)
  rw [← hB, ← hE] at h1
  rw [← hE, ← hE'] at h2
  have h4 : X * (B * Φ) = X * 1 := by
    calc X * (B * Φ) = B * (X * Φ) := by ring
      _ = B * (1 - E') := by rw [h3]
      _ = B * ((E - 1) * E') := by rw [sub_mul, h2, one_mul]
      _ = B * (E - 1) * E' := by ring
      _ = X * E * E' := by rw [h1]
      _ = X * 1 := by rw [mul_assoc, h2]
  have h5 : B * Φ = 1 := X_mul_cancel h4
  have hc : ∀ m, ∑ p ∈ antidiagonal m, phiCoeffQ p.1 * (bernoulli' p.2 / p.2.factorial) =
      if m = 0 then 1 else 0 := by
    intro m
    have h6 := congrArg (coeff m) h5
    rw [coeff_mul, coeff_one] at h6
    rw [← Finset.Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [← h6]
    refine sum_congr rfl fun p _ => ?_
    rw [hB, hΦ, coeff_mk, bernoulli'PowerSeries, coeff_mk]
    first
      | simp only [Algebra.algebraMap_self_apply]
      | simp only [algebraMap_self_apply]
    ring
  exact (eq_bplus_of_sum_antidiagonal (c := fun k => bernoulli' k / k.factorial) hc n).symm

end BCH
