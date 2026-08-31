import FabiusFunction.FabiusLegendreRationalEnergy
import FabiusFunction.FabiusLegendreRationalGram
import FabiusFunction.LegendreGaunt

/-!
# Finite Gaunt sums for the Rvachev Legendre Gram matrix

The executable rational even Legendre coefficients of Rvachev's `up`
function extend to a full coefficient sequence by inserting zero at every
odd index.  The resulting coefficient is the normalized rational Rvachev
moment of the corresponding ordinary Legendre polynomial.  Applying the
rational moment functional to the finite Legendre product linearization then
gives a finite Gaunt expansion of every rational Legendre Gram entry.

Reindexing the vanishing odd terms yields the even-coefficient form used in
the displayed Rvachev expansion.  Casting this identity entrywise gives the
same finite Gaunt sum for `upLegendreGramMatrix` for every bounded Fabius
representative satisfying `IsFabius`.

The Gaunt expansions themselves are finite polynomial and finite-sum
identities; their real forms use the existing moment--integral bridges.  This
module does not identify the Gaunt integrals with Wigner `3j` symbols or prove
the corresponding factorial formula, interchange an infinite Legendre series
with integration, or assert a Christoffel reconstruction.
-/

set_option autoImplicit false

open Finset Polynomial Set MeasureTheory
open scoped BigOperators Interval Polynomial

namespace Fabius

noncomputable section

/-! ## The full executable rational coefficient sequence -/

/-- The full rational Rvachev--Legendre coefficient sequence.  Its even
subsequence is `canonicalRvachevLegendreCoefficientRat`, and every odd entry
is zero. -/
def canonicalRvachevFullLegendreCoefficientRat (k : ℕ) : ℚ :=
  if 2 ∣ k then canonicalRvachevLegendreCoefficientRat (k / 2) else 0

/-- Restricting the full rational coefficient sequence to even indices
recovers the canonical even coefficient sequence. -/
@[simp]
theorem canonicalRvachevFullLegendreCoefficientRat_even (n : ℕ) :
    canonicalRvachevFullLegendreCoefficientRat (2 * n) =
      canonicalRvachevLegendreCoefficientRat n := by
  simp [canonicalRvachevFullLegendreCoefficientRat]

/-- Every odd entry of the full rational coefficient sequence vanishes. -/
@[simp]
theorem canonicalRvachevFullLegendreCoefficientRat_odd (n : ℕ) :
    canonicalRvachevFullLegendreCoefficientRat (2 * n + 1) = 0 := by
  simp [canonicalRvachevFullLegendreCoefficientRat,
    Nat.not_two_dvd_bit1]

/-- The canonical rational even coefficient casts to the analytic even
coefficient for every genuine bounded Fabius representative. -/
private theorem canonicalRvachevLegendreCoefficientRat_cast_of_isFabius
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (canonicalRvachevLegendreCoefficientRat n : ℝ) =
      rvachevLegendreCoefficient F n := by
  rw [rvachevLegendreCoefficient_eq_fabius_sum F hF n]
  unfold canonicalRvachevLegendreCoefficientRat
  push_cast
  apply congrArg₂ (· * ·) rfl
  apply Finset.sum_congr rfl
  intro k _hk
  rw [fabiusAtInverseTwoPow_cast F hF]

/-- Casting the full rational coefficient sequence to `ℝ` gives the full
analytic Fourier--Legendre coefficient for every genuine bounded Fabius
representative. -/
theorem canonicalRvachevFullLegendreCoefficientRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    (canonicalRvachevFullLegendreCoefficientRat k : ℝ) =
      rvachevFullLegendreCoefficient F k := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [canonicalRvachevFullLegendreCoefficientRat_even,
      canonicalRvachevLegendreCoefficientRat_cast_of_isFabius F hF,
      rvachevFullLegendreCoefficient_even_eq]
  · rw [canonicalRvachevFullLegendreCoefficientRat_odd,
      Rat.cast_zero,
      rvachevFullLegendreCoefficient_odd_eq_zero F hF]

/-! ## Normalized rational moments -/

/-- Casting the rational Rvachev moment functional gives the corresponding
polynomial integral against `rvachevUp` on its support interval. -/
private theorem momentFunctional_rvachevRawMomentRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (p : ℚ[X]) :
    (momentFunctional rvachevRawMomentRat p : ℝ) =
      ∫ x in (-1 : ℝ)..1,
        rvachevUp F x * (p.map (Rat.castHom ℝ)).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        (momentFunctional rvachevRawMomentRat (p + q) : ℝ) =
            (momentFunctional rvachevRawMomentRat p : ℝ) +
              (momentFunctional rvachevRawMomentRat q : ℝ) := by
                simp only [map_add, Rat.cast_add]
        _ = (∫ x in (-1 : ℝ)..1,
              rvachevUp F x * (p.map (Rat.castHom ℝ)).eval x) +
            ∫ x in (-1 : ℝ)..1,
              rvachevUp F x * (q.map (Rat.castHom ℝ)).eval x := by
                rw [hp, hq]
        _ = ∫ x in (-1 : ℝ)..1,
              rvachevUp F x * (p.map (Rat.castHom ℝ)).eval x +
                rvachevUp F x * (q.map (Rat.castHom ℝ)).eval x := by
            have hpInt : IntervalIntegrable
                (fun x : ℝ ↦
                  rvachevUp F x * (p.map (Rat.castHom ℝ)).eval x)
                MeasureTheory.volume (-1) 1 :=
              ((rvachev_contDiff F hF).continuous.mul
                (p.map (Rat.castHom ℝ)).continuous).intervalIntegrable _ _
            have hqInt : IntervalIntegrable
                (fun x : ℝ ↦
                  rvachevUp F x * (q.map (Rat.castHom ℝ)).eval x)
                MeasureTheory.volume (-1) 1 :=
              ((rvachev_contDiff F hF).continuous.mul
                (q.map (Rat.castHom ℝ)).continuous).intervalIntegrable _ _
            symm
            exact intervalIntegral.integral_add hpInt hqInt
        _ = ∫ x in (-1 : ℝ)..1,
              rvachevUp F x * ((p + q).map (Rat.castHom ℝ)).eval x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simp [mul_add]
  | monomial n a =>
      have hsupport :
          Function.support (fun x : ℝ ↦ x ^ n * rvachevUp F x) ⊆
            Ioc (-1 : ℝ) 1 := by
        intro x hx
        have hup : rvachevUp F x ≠ 0 := by
          intro hzero
          apply hx
          simp [hzero]
        exact Ioo_subset_Ioc_self (support_rvachev_subset_Ioo F hF hup)
      calc
        (momentFunctional rvachevRawMomentRat
            (Polynomial.monomial n a) : ℝ) =
            (a : ℝ) * (rvachevRawMomentRat n : ℝ) := by
              simp only [momentFunctional_monomial, Rat.cast_mul]
        _ = (a : ℝ) * ∫ x : ℝ, x ^ n * rvachevUp F x := by
              rw [integral_pow_mul_rvachev_eq_rvachevRawMomentRat_cast
                F hF n]
        _ = (a : ℝ) * ∫ x in (-1 : ℝ)..1,
              x ^ n * rvachevUp F x := by
              rw [intervalIntegral.integral_eq_integral_of_support_subset
                hsupport]
        _ = ∫ x in (-1 : ℝ)..1,
              (a : ℝ) * (x ^ n * rvachevUp F x) := by
              rw [intervalIntegral.integral_const_mul]
        _ = ∫ x in (-1 : ℝ)..1,
              rvachevUp F x *
                ((Polynomial.monomial n a).map (Rat.castHom ℝ)).eval x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simp [mul_comm, mul_assoc]

/-- The full rational Rvachev--Legendre coefficient is the normalized
Rvachev moment of the corresponding rational Legendre polynomial. -/
theorem canonicalRvachevFullLegendreCoefficientRat_eq_normalized_moment
    (k : ℕ) :
    canonicalRvachevFullLegendreCoefficientRat k =
      (((2 * k + 1 : ℕ) : ℚ) / 2) *
        momentFunctional rvachevRawMomentRat (legendrePolynomialRat k) := by
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [canonicalRvachevFullLegendreCoefficientRat_cast fabius fabius_spec,
    momentFunctional_rvachevRawMomentRat_cast fabius fabius_spec,
    legendrePolynomialRat_cast]
  unfold rvachevFullLegendreCoefficient
  congr 1
  push_cast
  rfl

/-! ## Finite rational Gaunt sums -/

/-- A finite sum supported on even indices can be reindexed by half of its
index. -/
private lemma sum_range_even_div_two {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : ℕ → R) :
    (∑ x ∈ range (n + 1), if 2 ∣ x then f (x / 2) else 0) =
      ∑ k ∈ range (n / 2 + 1), f k := by
  rw [← Finset.sum_filter]
  have hfilter :
      (range (n + 1)).filter (fun x ↦ 2 ∣ x) =
        (range (n / 2 + 1)).image (fun k ↦ 2 * k) := by
    ext x
    simp only [mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, rfl⟩
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨by omega, ⟨k, rfl⟩⟩
  rw [hfilter, Finset.sum_image]
  · simp
  · intro a _ha b _hb hab
    change 2 * a = 2 * b at hab
    omega

/-- Every executable rational Rvachev Legendre Gram entry is the finite
Gaunt sum against the full rational Legendre coefficient sequence. -/
theorem rvachevLegendreGramEntryRat_eq_sum_full_gaunt (i j : ℕ) :
    rvachevLegendreGramEntryRat i j =
      ∑ k ∈ range (i + j + 1),
        canonicalRvachevFullLegendreCoefficientRat k *
          legendreGauntRat i j k := by
  rw [rvachevLegendreGramEntryRat_eq_momentPairing,
    momentPairing_apply, legendrePolynomialRat_mul_eq_sum_gaunt,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_smul, smul_eq_mul, legendreProductLinearizationCoeffRat,
    canonicalRvachevFullLegendreCoefficientRat_eq_normalized_moment]
  ring

/-- Removing the zero odd coefficients gives the finite even-indexed Gaunt
sum for every executable rational Rvachev Legendre Gram entry. -/
theorem rvachevLegendreGramEntryRat_eq_sum_gaunt (i j : ℕ) :
    rvachevLegendreGramEntryRat i j =
      ∑ r ∈ range ((i + j) / 2 + 1),
        canonicalRvachevLegendreCoefficientRat r *
          legendreGauntRat i j (2 * r) := by
  calc
    rvachevLegendreGramEntryRat i j =
        ∑ k ∈ range (i + j + 1),
          canonicalRvachevFullLegendreCoefficientRat k *
            legendreGauntRat i j k :=
      rvachevLegendreGramEntryRat_eq_sum_full_gaunt i j
    _ = ∑ k ∈ range (i + j + 1),
          if 2 ∣ k then
            canonicalRvachevLegendreCoefficientRat (k / 2) *
              legendreGauntRat i j (2 * (k / 2))
          else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hdiv : 2 ∣ k
      · simp only [canonicalRvachevFullLegendreCoefficientRat,
          if_pos hdiv]
        rw [Nat.mul_div_cancel' hdiv]
      · simp [canonicalRvachevFullLegendreCoefficientRat, hdiv]
    _ = ∑ r ∈ range ((i + j) / 2 + 1),
          canonicalRvachevLegendreCoefficientRat r *
            legendreGauntRat i j (2 * r) :=
      sum_range_even_div_two (i + j)
        (fun r ↦ canonicalRvachevLegendreCoefficientRat r *
          legendreGauntRat i j (2 * r))

/-! ## Matrix forms and the real cast -/

/-- Entry formula for the executable rational Legendre Gram matrix in terms
of the finite even-indexed Gaunt sum. -/
theorem rvachevLegendreGramMatrixRat_apply_eq_sum_gaunt
    (n : ℕ) (i j : Fin n) :
    rvachevLegendreGramMatrixRat n i j =
      ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
        canonicalRvachevLegendreCoefficientRat r *
          legendreGauntRat (i : ℕ) (j : ℕ) (2 * r) := by
  simpa only [rvachevLegendreGramMatrixRat_apply] using
    rvachevLegendreGramEntryRat_eq_sum_gaunt (i : ℕ) (j : ℕ)

/-- Every entry of the real up-law Legendre Gram matrix is the finite Gaunt
sum against the analytic even Rvachev--Legendre coefficients. -/
theorem upLegendreGramMatrix_apply_eq_sum_gaunt
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (i j : Fin n) :
    upLegendreGramMatrix F n i j =
      ∑ r ∈ range (((i : ℕ) + (j : ℕ)) / 2 + 1),
        rvachevLegendreCoefficient F r *
          legendreGaunt (i : ℕ) (j : ℕ) (2 * r) := by
  rw [upLegendreGramMatrix, polynomialMomentGramMatrix_apply,
    ← rvachevLegendreGramEntryRat_cast F hF (i : ℕ) (j : ℕ),
    rvachevLegendreGramEntryRat_eq_sum_gaunt]
  push_cast
  apply Finset.sum_congr rfl
  intro r _hr
  rw [canonicalRvachevLegendreCoefficientRat_cast_of_isFabius F hF,
    legendreGauntRat_cast]

end

end Fabius
