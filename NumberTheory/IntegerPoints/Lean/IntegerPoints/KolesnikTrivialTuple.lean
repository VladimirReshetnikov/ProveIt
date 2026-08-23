import IntegerPoints.Kolesnik

/-!
# Kolesnik's trivial exponent tuple

This module proves that `(0 | 1, ..., 1)` belongs to every several-variable
exponent class.  The only analytic input is the triangle inequality: an
exponential sum is bounded by the number of lattice points in its domain.
The latter is bounded by the enclosing dyadic box, with at most `3 * X j`
integer choices in coordinate `j`.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace KolesnikTrivial

/-- A finite integer box containing every lattice point of a dyadic box with
positive side lengths. -/
noncomputable def integerBox {n : ℕ} (X : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc 0 (⌊2 * X j⌋₊ : ℤ)

theorem mem_integerBox_of_mem_latticePoints {n : ℕ} {X : Fin n → ℝ}
    {D : Set (Fin n → ℝ)} (hX : ∀ j, 1 ≤ X j) (hD : D ⊆ dyadicBox X)
    {x : Fin n → ℤ} (hx : x ∈ latticePoints D) : x ∈ integerBox X := by
  rw [integerBox, Fintype.mem_piFinset]
  intro j
  have hxD : realVec x ∈ D := hx
  have hxj := hD hxD j
  change X j ≤ (x j : ℝ) ∧ (x j : ℝ) ≤ 2 * X j at hxj
  have hXj : 1 ≤ X j := hX j
  have hxj0Real : (0 : ℝ) ≤ (x j : ℝ) := by linarith [hXj, hxj.1]
  have hxj0 : (0 : ℤ) ≤ x j := by exact_mod_cast hxj0Real
  have htoNat : ((x j).toNat : ℤ) = x j := Int.toNat_of_nonneg hxj0
  have htoNatReal : (((x j).toNat : ℕ) : ℝ) ≤ 2 * X j := by
    rw [show (((x j).toNat : ℕ) : ℝ) = (x j : ℝ) by exact_mod_cast htoNat]
    exact hxj.2
  have hupperNat : (x j).toNat ≤ ⌊2 * X j⌋₊ := Nat.le_floor htoNatReal
  have hupper : x j ≤ (⌊2 * X j⌋₊ : ℤ) := by
    rw [← htoNat]
    exact_mod_cast hupperNat
  exact Finset.mem_Icc.mpr ⟨hxj0, hupper⟩

/-- The enclosing integer box has at most `3^n * ∏ j, X j` points. -/
theorem card_integerBox_le {n : ℕ} {X : Fin n → ℝ} (hX : ∀ j, 1 ≤ X j) :
    (integerBox X).card ≤ (3 : ℝ) ^ n * totalProduct X := by
  calc
    ((integerBox X).card : ℝ) =
        ∏ j, ((⌊2 * X j⌋₊ + 1 : ℕ) : ℝ) := by
      rw [integerBox, Fintype.card_piFinset]
      push_cast
      apply Finset.prod_congr rfl
      intro j _
      simp [Int.card_Icc]
    _ ≤ ∏ j, 3 * X j := by
      apply Finset.prod_le_prod
      · intro j _
        exact Nat.cast_nonneg _
      · intro j _
        have hj0 : 0 ≤ 2 * X j := by linarith [hX j]
        have hfloor := Nat.floor_le hj0
        push_cast
        linarith [hX j, hfloor]
    _ = (3 : ℝ) ^ n * totalProduct X := by
      rw [Finset.prod_mul_distrib]
      simp [totalProduct]

/-- The norm of a lattice exponential sum is bounded by the enclosing box. -/
theorem norm_latticeSum_le_card_integerBox {n : ℕ} {X : Fin n → ℝ}
    {D : Set (Fin n → ℝ)} (hX : ∀ j, 1 ≤ X j) (hD : D ⊆ dyadicBox X)
    (f : (Fin n → ℝ) → ℝ) :
    ‖latticeSum D f‖ ≤ (integerBox X).card := by
  let summand : (Fin n → ℤ) → ℂ :=
    Set.indicator (latticePoints D) fun x => e (f (realVec x))
  have hsupp : Function.support summand ⊆ ↑(integerBox X) := by
    intro x hx
    apply mem_integerBox_of_mem_latticePoints hX hD
    by_contra hxD
    have hsummand : summand x = 0 := by simp [summand, hxD]
    exact hx hsummand
  have he (t : ℝ) : ‖e t‖ = 1 := by
    rw [e, Complex.norm_exp]
    simp
  rw [latticeSum, show
    (fun x => Set.indicator (latticePoints D) (fun y => e (f (realVec y))) x) =
      summand from rfl,
    finsum_eq_sum_of_support_subset summand hsupp]
  calc
    ‖∑ x ∈ integerBox X, summand x‖ ≤
        ∑ x ∈ integerBox X, ‖summand x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ integerBox X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hxD : x ∈ latticePoints D
      · rw [show summand x = e (f (realVec x)) by
          simp [summand, Set.indicator_of_mem hxD], he]
      · simp [summand, hxD]
    _ = (integerBox X).card := by simp

end KolesnikTrivial

/-- Kolesnik's trivial exponent tuple `(0 | 1, ..., 1)` belongs to `E_n` in
every dimension. -/
theorem kolesnik_trivialTuple_holds : kolesnik_trivialTuple := by
  intro n
  refine ⟨by norm_num, fun _ => by norm_num, ?_⟩
  intro α _hα C₀
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε
  refine ⟨(3 : ℝ) ^ n, ?_⟩
  intro F X D f hX _hF _hXF hD _hf
  have hnorm := KolesnikTrivial.norm_latticeSum_le_card_integerBox hX hD.1 f
  have hcard := KolesnikTrivial.card_integerBox_le hX
  have htotal : 1 ≤ totalProduct X := by
    rw [totalProduct]
    exact Finset.one_le_prod fun j _ => hX j
  have htotal0 : 0 ≤ totalProduct X := zero_le_one.trans htotal
  have hpow : 1 ≤ totalProduct X ^ ε := Real.one_le_rpow htotal hε.le
  calc
    ‖latticeSum D f‖ ≤ (KolesnikTrivial.integerBox X).card := hnorm
    _ ≤ (3 : ℝ) ^ n * totalProduct X := hcard
    _ = (3 : ℝ) ^ n * 1 * totalProduct X := by ring
    _ ≤ (3 : ℝ) ^ n * totalProduct X ^ ε * totalProduct X :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) htotal0
    _ = (3 : ℝ) ^ n * totalProduct X ^ ε * F ^ (0 : ℝ) *
        ∏ j, X j ^ (1 : ℝ) := by
      simp [totalProduct]

end LeanProofs.IntegerPoints
