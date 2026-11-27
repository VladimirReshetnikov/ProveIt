import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Valuation.Basic

/-!
# Moments of a sparse polynomial

This formalizes the algebraic part of the local root count (smd:lem:disk) in
Analysis/GeneralizedRiemannHypothesis/Article/sections/smd.tex. For term
coefficients cᵢ, exponents nᵢ, and center a, the input weights are cᵢ aⁿⁱ.
The moment sequence has a nonzero initial value and its characteristic
polynomial bounds all later values under a nonarchimedean valuation.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators
open Polynomial

variable {t : ℕ} {K : Type*}

/-- The coefficient moment occurring in the exponential substitution. -/
def moment [Semiring K] (n : Fin t → ℕ) (a : Fin t → K) (k : ℕ) : K :=
  ∑ i, a i * (n i : K) ^ k

theorem exists_nonzero_initial_moment [CommRing K] [IsDomain K] [CharZero K]
    (n : Fin t → ℕ) (a : Fin t → K) (hn : Function.Injective n) (ha : a ≠ 0) :
    ∃ k : Fin t, moment n a k ≠ 0 := by
  classical
  by_contra! h
  apply ha
  let nodes : Fin t → K := fun i => n i
  have hnodes : Function.Injective nodes := fun _ _ e => hn (Nat.cast_injective e)
  refine Matrix.eq_zero_of_vecMul_eq_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes) ?_
  funext k
  simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, moment, nodes] using h k

/-- The integral monic polynomial that annihilates the exponent nodes. -/
noncomputable def exponentPolynomial (n : Fin t → ℕ) : ℤ[X] :=
  ∏ i, (X - C (n i : ℤ))

theorem exponentPolynomial_monic (n : Fin t → ℕ) :
    (exponentPolynomial n).Monic :=
  monic_prod_of_monic Finset.univ _ (fun i _ => monic_X_sub_C (n i : ℤ))

@[simp]
theorem exponentPolynomial_natDegree (n : Fin t → ℕ) :
    (exponentPolynomial n).natDegree = t := by
  unfold exponentPolynomial
  rw [natDegree_prod_of_monic Finset.univ _ (fun i _ => monic_X_sub_C (n i : ℤ))]
  calc
    ∑ i, (X - C (n i : ℤ)).natDegree = ∑ _ : Fin t, (1 : ℕ) :=
      Finset.sum_congr rfl (fun _ _ => natDegree_X_sub_C _)
    _ = t := by simp

private theorem eval₂_exponentPolynomial [CommRing K] (n : Fin t → ℕ) (i : Fin t) :
    (exponentPolynomial n).eval₂ (Int.castRingHom K) (n i : K) = 0 := by
  rw [exponentPolynomial, eval₂_finsetProd]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

private theorem moment_annihilation [CommRing K] (n : Fin t → ℕ) (a : Fin t → K) (k : ℕ) :
    (∑ j ∈ Finset.range (t + 1),
      ((exponentPolynomial n).coeff j : K) * moment n a (k + j)) = 0 := by
  calc
    _ = ∑ i, (a i * (n i : K) ^ k) *
        ∑ j ∈ Finset.range (t + 1), ((exponentPolynomial n).coeff j : K) * (n i : K) ^ j := by
          simp_rw [moment, Finset.mul_sum, pow_add]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ =>
            Finset.sum_congr rfl (fun _ _ => by ring))
    _ = 0 := by
      have heval (i : Fin t) : (∑ j ∈ Finset.range (t + 1),
          ((exponentPolynomial n).coeff j : K) * (n i : K) ^ j) = 0 := by
        simpa [eval₂_eq_sum_range] using (eval₂_exponentPolynomial (K := K) n i)
      simp only [heval, mul_zero, Finset.sum_const_zero]

theorem moment_recurrence [CommRing K] (n : Fin t → ℕ) (a : Fin t → K) (k : ℕ) :
    moment n a (k + t) =
      -(∑ j ∈ Finset.range t, ((exponentPolynomial n).coeff j : K) * moment n a (k + j)) := by
  have lead : (exponentPolynomial n).coeff t = 1 := by
    simpa using (exponentPolynomial_monic n).coeff_natDegree
  have h := moment_annihilation n a k
  rw [Finset.sum_range_succ, lead, Int.cast_one, one_mul] at h
  exact eq_neg_of_add_eq_zero_right h

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private theorem valuation_natCast_le_one [Ring K] (v : Valuation K Γ₀) (n : ℕ) :
    v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_add_le ih (by simp)

private theorem valuation_intCast_le_one [Ring K] (v : Valuation K Γ₀) (z : ℤ) :
    v (z : K) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, v.map_neg]
    exact valuation_natCast_le_one v (n + 1)

/-- Every moment is bounded by any common bound for the initial moments. -/
theorem valuation_moment_le [CommRing K] (v : Valuation K Γ₀)
    (n : Fin t → ℕ) (a : Fin t → K) (B : Γ₀)
    (h : ∀ j < t, v (moment n a j) ≤ B) (k : ℕ) : v (moment n a k) ≤ B := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < t
    · exact h k hk
    have hstep := moment_recurrence n a (k - t)
    rw [Nat.sub_add_cancel (Nat.le_of_not_gt hk)] at hstep
    rw [hstep, v.map_neg]
    apply v.map_sum_le
    intro j hj
    have hjt := Finset.mem_range.mp hj
    rw [map_mul]
    exact (mul_le_mul_left (valuation_intCast_le_one v _) _).trans
      (by simpa using ih (k - t + j) (by omega))

/-- A nonzero initial moment has maximal valuation among all the moments, in
the multiplicative valuation convention. -/
theorem exists_dominating_initial_moment [Field K] [CharZero K]
    (v : Valuation K Γ₀) (n : Fin t → ℕ) (a : Fin t → K)
    (hn : Function.Injective n) (ha : a ≠ 0) :
    ∃ j : Fin t, v (moment n a j) ≠ 0 ∧ ∀ k, v (moment n a k) ≤ v (moment n a j) := by
  obtain ⟨i, hi⟩ := exists_nonzero_initial_moment n a hn ha
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin t => v (moment n a j)) ⟨i, Finset.mem_univ i⟩
  refine ⟨j, ?_, valuation_moment_le v n a _ (fun k hk => hj ⟨k, hk⟩ (Finset.mem_univ _))⟩
  intro hz
  exact (map_ne_zero v).mpr hi (le_antisymm (hz ▸ hj i (Finset.mem_univ i)) zero_le)

/-- A coefficient of the series after the substitution x = a exp(bY). -/
def exponentialCoefficient [Field K] (n : Fin t → ℕ) (c : Fin t → K) (a b : K) (k : ℕ) :
    K :=
  moment n (fun i => c i * a ^ n i) k * (b ^ k / (k.factorial : K))

/-- Outside the range where the factorial weight can compete with the initial
weights, the corresponding coefficient has strictly smaller valuation than
one fixed nonzero initial coefficient. -/
theorem exists_initial_coefficient_dominating_small_weights [Field K] [CharZero K]
    (v : Valuation K Γ₀) (n : Fin t → ℕ) (c : Fin t → K) (a b : K)
    (hn : Function.Injective n) (hc : c ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ j : Fin t, exponentialCoefficient n c a b j ≠ 0 ∧ ∀ k : ℕ,
      (∀ i : Fin t, v (b ^ k / (k.factorial : K)) <
        v (b ^ (i : ℕ) / ((i : ℕ).factorial : K))) →
      v (exponentialCoefficient n c a b k) < v (exponentialCoefficient n c a b j) := by
  let weights := fun i => c i * a ^ n i
  have hweights : weights ≠ 0 := by
    intro hz
    apply hc
    funext i
    exact (mul_eq_zero.mp (congrFun hz i)).resolve_right (pow_ne_zero _ ha)
  obtain ⟨j, hj, hmax⟩ := exists_dominating_initial_moment v n weights hn hweights
  refine ⟨j, mul_ne_zero (fun h => hj (h ▸ map_zero v))
    (div_ne_zero (pow_ne_zero _ hb) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))), ?_⟩
  intro k hk
  simp only [exponentialCoefficient, map_mul]
  exact (mul_le_mul_left (hmax k) _).trans_lt
    (mul_lt_mul_of_pos_left (hk j) (pos_iff_ne_zero.mpr hj))

end GRHArticle.SingularModuli
