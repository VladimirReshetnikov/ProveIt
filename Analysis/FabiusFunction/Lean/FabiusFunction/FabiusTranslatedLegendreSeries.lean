import FabiusFunction.FabiusLegendreSeries

/-!
# A translated Legendre series for the signed global Fabius function

The even Fourier--Legendre expansion of Rvachev's `up` function on `[-1,1]`
can be translated to `[0,2]`.  On this interval the signed global Fabius
function is the single translate `up(x - 1)`.  Expanding the shifted even
Legendre polynomial into monomials gives the exact double finite sum inside
the resulting infinite series.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

noncomputable section

/-! ## The translated series before specializing its coefficients -/

/-- Translation of the even Legendre series from `[-1,1]` to `[0,2]`.
This factorized form works for every bounded Fabius function satisfying its
defining characterization. -/
theorem hasSum_extendedFabius_translatedLegendreSeries
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    HasSum (fun n ↦
      rvachevLegendreCoefficient F n *
        ∑ j ∈ range (2 * n + 1),
          (-1 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j *
            (2 * n).choose j * (j + 2 * n).choose j * x ^ j)
      (extendedFabius F x) := by
  have hxshift : x - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hseries := hasSum_rvachevLegendreSeries F hF (x - 1) hxshift
  have hext : extendedFabius F x = rvachevUp F (x - 1) :=
    extendedFabius_eq_rvachevUp_sub_one F hF hx.2
  rw [hext]
  convert hseries using 1
  funext n
  rw [eval_legendrePolynomial_even_sub_one]

/-- Tsum form of `hasSum_extendedFabius_translatedLegendreSeries`. -/
theorem tsum_extendedFabius_translatedLegendreSeries
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    (∑' n,
      rvachevLegendreCoefficient F n *
        ∑ j ∈ range (2 * n + 1),
          (-1 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j *
            (2 * n).choose j * (j + 2 * n).choose j * x ^ j) =
      extendedFabius F x :=
  (hasSum_extendedFabius_translatedLegendreSeries F hF x hx).tsum_eq

/-! ## Exact canonical coefficients -/

private lemma translatedLegendre_two_power (n j k : ℕ) :
    ((4 : ℝ)⁻¹ ^ n) *
          (2 : ℝ) ^ (2 * k + 1).choose 2 *
          ((2 : ℝ)⁻¹ ^ j) =
      (2 : ℝ) ^
        ((k : ℤ) - (j : ℤ) + 2 * (k : ℤ) ^ 2 - 2 * (n : ℤ)) := by
  have hchoose : (2 * k + 1).choose 2 = 2 * k ^ 2 + k := by
    rw [Nat.choose_two_right]
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hsub]
    have hmul : (2 * k + 1) * (2 * k) =
        (2 * k ^ 2 + k) * 2 := by ring_nf
    rw [hmul]
    simp
  rw [hchoose]
  have hfour : (4 : ℝ)⁻¹ = (2 : ℝ) ^ (-2 : ℤ) := by
    norm_num [zpow_neg]
  have hhalf : (2 : ℝ)⁻¹ = (2 : ℝ) ^ (-1 : ℤ) := by
    norm_num [zpow_neg]
  rw [hfour, hhalf]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast]
  rw [← zpow_mul, ← zpow_mul]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring_nf

private lemma two_zpow_neg_two_mul_sub_one (k : ℕ) :
    (2 : ℝ) ^ (-(2 * (k : ℤ)) - 1) =
      ((2 : ℝ) ^ (2 * k + 1))⁻¹ := by
  rw [← zpow_natCast, ← zpow_neg]
  congr 1
  push_cast
  ring_nf

private lemma globalFabius_two_zpow_neg_two_mul_sub_one (k : ℕ) :
    globalFabius ((2 : ℝ) ^ (-(2 * (k : ℤ)) - 1)) =
      fabiusReal fabius ((2 : ℝ) ^ (-(2 * (k : ℤ)) - 1)) := by
  rw [globalFabius]
  apply extendedFabius_eq_fabiusReal fabius fabius_spec
  rw [two_zpow_neg_two_mul_sub_one]
  constructor
  · positivity
  · exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))

private theorem hasSum_globalFabius_translatedLegendre_formula_jk
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    HasSum (fun n ↦
      ∑ j ∈ range (2 * n + 1),
        ∑ k ∈ range (n + 1),
          (-1 : ℝ) ^ (j + k + n) *
            (2 : ℝ) ^
              ((k : ℤ) - (j : ℤ) +
                2 * (k : ℤ) ^ 2 - 2 * (n : ℤ)) *
            ((4 * n + 1 : ℕ) : ℝ) *
            (2 * n).choose j *
            (2 * n).choose (k + n) *
            (2 * k + 2 * n).choose (2 * n) *
            (j + 2 * n).choose j *
            (Nat.factorial (2 * k) : ℝ) *
            globalFabius ((2 : ℝ) ^ (-(2 * (k : ℤ)) - 1)) *
            x ^ j)
      (globalFabius x) := by
  have hseries := hasSum_extendedFabius_translatedLegendreSeries
    fabius fabius_spec x hx
  rw [show globalFabius x = extendedFabius fabius x by rfl]
  convert hseries using 1
  funext n
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro k hk
  rw [globalFabius_two_zpow_neg_two_mul_sub_one]
  rw [two_zpow_neg_two_mul_sub_one]
  rw [← translatedLegendre_two_power n j k]
  rw [show (-1 : ℝ) ^ (j + k + n) =
      (-1 : ℝ) ^ (n + k) * (-1 : ℝ) ^ j by
    rw [pow_add, pow_add]
    ring_nf]
  ring_nf

/-- The exact translated-Legendre representation of the canonical signed
global Fabius function on `[0,2]`.  Both finite sums include their upper
endpoints.  The integer exponent on `2` is the literal exponent in the
displayed Wolfram Language formula.  At `x = 0`, Lean's natural-power
convention gives `0 ^ 0 = 1`, as assumed in the claim. -/
theorem hasSum_globalFabius_translatedLegendre_formula
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    HasSum (fun n ↦
      ∑ k ∈ range (n + 1),
        ∑ j ∈ range (2 * n + 1),
          (-1 : ℝ) ^ (j + k + n) *
            (2 : ℝ) ^
              ((k : ℤ) - (j : ℤ) +
                2 * (k : ℤ) ^ 2 - 2 * (n : ℤ)) *
            ((4 * n + 1 : ℕ) : ℝ) *
            (2 * n).choose j *
            (2 * n).choose (k + n) *
            (2 * k + 2 * n).choose (2 * n) *
            (j + 2 * n).choose j *
            (Nat.factorial (2 * k) : ℝ) *
            globalFabius ((2 : ℝ) ^ (-(2 * (k : ℤ)) - 1)) *
            x ^ j)
      (globalFabius x) := by
  convert hasSum_globalFabius_translatedLegendre_formula_jk x hx using 1
  funext n
  rw [Finset.sum_comm]

/-- Tsum equality for the exact translated-Legendre formula. -/
theorem tsum_globalFabius_translatedLegendre_formula
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    (∑' n,
      ∑ k ∈ range (n + 1),
        ∑ j ∈ range (2 * n + 1),
          (-1 : ℝ) ^ (j + k + n) *
            (2 : ℝ) ^
              ((k : ℤ) - (j : ℤ) +
                2 * (k : ℤ) ^ 2 - 2 * (n : ℤ)) *
            ((4 * n + 1 : ℕ) : ℝ) *
            (2 * n).choose j *
            (2 * n).choose (k + n) *
            (2 * k + 2 * n).choose (2 * n) *
            (j + 2 * n).choose j *
            (Nat.factorial (2 * k) : ℝ) *
            globalFabius ((2 : ℝ) ^ (-(2 * (k : ℤ)) - 1)) *
            x ^ j) = globalFabius x :=
  (hasSum_globalFabius_translatedLegendre_formula x hx).tsum_eq

/-- Wolfram-style orientation of
`tsum_globalFabius_translatedLegendre_formula`. -/
theorem globalFabius_eq_tsum_translatedLegendre_formula
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) :
    globalFabius x =
      ∑' n,
        ∑ k ∈ range (n + 1),
          ∑ j ∈ range (2 * n + 1),
            (-1 : ℝ) ^ (j + k + n) *
              (2 : ℝ) ^
                ((k : ℤ) - (j : ℤ) +
                  2 * (k : ℤ) ^ 2 - 2 * (n : ℤ)) *
              ((4 * n + 1 : ℕ) : ℝ) *
              (2 * n).choose j *
              (2 * n).choose (k + n) *
              (2 * k + 2 * n).choose (2 * n) *
              (j + 2 * n).choose j *
              (Nat.factorial (2 * k) : ℝ) *
              globalFabius ((2 : ℝ) ^ (-(2 * (k : ℤ)) - 1)) *
              x ^ j :=
  (tsum_globalFabius_translatedLegendre_formula x hx).symm

end

end Fabius
