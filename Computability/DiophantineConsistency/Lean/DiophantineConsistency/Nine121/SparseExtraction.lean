import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Sparse coefficient extraction for shared-position kernels

Package 101's (and the H1868) layouts share one kernel position between
several rows, so the one-position-per-record framework of
`DegreeSeparatedCoding` does not apply. Here the word `U = Σ uᵢ X^{wᵢ}` and a
kernel `K = Σ c_p X^{pos_p}` are expanded into monomials indexed by
`Fin n × Fin n × Fin m` (`quad_expand`) or `Fin n × Fin m` (`lin_expand`), and
a coefficient is the sum over an explicit finset `S` of the indices landing at
the exponent (`coeff_sum_monomial`; the membership condition is a finite
decidable fact). In a linearly ordered ring every coefficient is bounded by
`H (Σ uᵢ)²`, `H Σ uᵢ` and `H` when `|c_p| ≤ H` and the positions are distinct
(`abs_coeff_quad_le`, `abs_coeff_lin_le`, `abs_coeff_const_le`). -/
set_option autoImplicit false
noncomputable section
namespace Nine121.SparseExtraction
open Polynomial
open scoped BigOperators

section Ring
variable {R : Type*} [CommRing R]

def wordPoly {n : ℕ} (w : Fin n → ℕ) (u : Fin n → R) : R[X] := ∑ i, monomial (w i) (u i)

def kernelPoly {m : ℕ} (pos : Fin m → ℕ) (c : Fin m → R) : R[X] := ∑ p, monomial (pos p) (c p)

theorem coeff_sum_monomial {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (m : ι → R)
    (E : ℕ) (S : Finset ι) (hS : ∀ t, e t = E ↔ t ∈ S) :
    (∑ t, monomial (e t) (m t)).coeff E = ∑ t ∈ S, m t := by
  rw [finset_sum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext t
  simp [hS t]

theorem coeff_sum_monomial_eq_zero {ι : Type*} [Fintype ι] (e : ι → ℕ) (m : ι → R) (E : ℕ)
    (hE : ∀ t, e t ≠ E) : (∑ t, monomial (e t) (m t)).coeff E = 0 := by
  rw [finset_sum_coeff]
  simp only [coeff_monomial]
  exact Finset.sum_eq_zero (fun t _ => if_neg (hE t))

theorem quad_expand {n m : ℕ} (w : Fin n → ℕ) (u : Fin n → R) (pos : Fin m → ℕ) (c : Fin m → R) :
    wordPoly w u ^ 2 * kernelPoly pos c =
      ∑ t : Fin n × Fin n × Fin m,
        monomial (w t.1 + w t.2.1 + pos t.2.2) (u t.1 * u t.2.1 * c t.2.2) := by
  rw [pow_two]
  simp only [wordPoly, kernelPoly]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum, monomial_mul_monomial]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

theorem lin_expand {n m : ℕ} (w : Fin n → ℕ) (u : Fin n → R) (pos : Fin m → ℕ) (c : Fin m → R) :
    wordPoly w u * kernelPoly pos c =
      ∑ t : Fin n × Fin m, monomial (w t.1 + pos t.2) (u t.1 * c t.2) := by
  simp only [wordPoly, kernelPoly]
  rw [Finset.sum_mul_sum]
  simp only [monomial_mul_monomial]
  rw [Fintype.sum_prod_type]

theorem eval_wordPoly {n : ℕ} (w : Fin n → ℕ) (u : Fin n → R) (B : R) :
    (wordPoly w u).eval B = ∑ i, u i * B ^ w i := by
  simp [wordPoly, eval_finsetSum]

theorem eval_kernelPoly {m : ℕ} (pos : Fin m → ℕ) (c : Fin m → R) (B : R) :
    (kernelPoly pos c).eval B = ∑ p, c p * B ^ pos p := by
  simp [kernelPoly, eval_finsetSum]

end Ring

section Order
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A sum with at most one live term is bounded by the bound of that term. -/
theorem sum_ite_le_of_unique {m : ℕ} (P : Fin m → Prop) [DecidablePred P] (f : Fin m → R)
    (K : R) (hK : 0 ≤ K) (hf : ∀ p, f p ≤ K) (hP : ∀ p q, P p → P q → p = q) :
    ∑ p, (if P p then f p else 0) ≤ K := by
  by_cases h : ∃ p, P p
  · obtain ⟨p, hp⟩ := h
    rw [Finset.sum_eq_single p]
    · rw [if_pos hp]; exact hf p
    · intro q _ hq
      rw [if_neg]
      intro hq'
      exact hq (hP q p hq' hp)
    · intro hp'; exact absurd (Finset.mem_univ p) hp'
  · push Not at h
    rw [Finset.sum_eq_zero (fun p _ => if_neg (h p))]
    exact hK

theorem abs_coeff_quad_le {n m : ℕ} (w : Fin n → ℕ) (u : Fin n → R) (hu : ∀ i, 0 ≤ u i)
    (pos : Fin m → ℕ) (hpos : Function.Injective pos) (c : Fin m → R) (H : R) (hH : 0 ≤ H)
    (hc : ∀ p, |c p| ≤ H) (e : ℕ) :
    |(wordPoly w u ^ 2 * kernelPoly pos c).coeff e| ≤ H * (∑ i, u i) ^ 2 := by
  rw [quad_expand, finset_sum_coeff]
  simp only [coeff_monomial]
  calc |∑ t : Fin n × Fin n × Fin m,
        if w t.1 + w t.2.1 + pos t.2.2 = e then u t.1 * u t.2.1 * c t.2.2 else 0|
      ≤ ∑ t : Fin n × Fin n × Fin m,
        |if w t.1 + w t.2.1 + pos t.2.2 = e then u t.1 * u t.2.1 * c t.2.2 else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, ∑ p,
        (if w i + w j + pos p = e then u i * u j * |c p| else 0) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun p _ => ?_))
        split_ifs
        · rw [abs_mul, abs_mul, abs_of_nonneg (hu i), abs_of_nonneg (hu j)]
        · exact abs_zero
    _ ≤ ∑ i, ∑ j, u i * u j * H := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        apply sum_ite_le_of_unique _ _ _ (mul_nonneg (mul_nonneg (hu i) (hu j)) hH)
        · intro p
          exact mul_le_mul_of_nonneg_left (hc p) (mul_nonneg (hu i) (hu j))
        · intro p q hp hq
          apply hpos
          omega
    _ = H * (∑ i, u i) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

theorem abs_coeff_lin_le {n m : ℕ} (w : Fin n → ℕ) (u : Fin n → R) (hu : ∀ i, 0 ≤ u i)
    (pos : Fin m → ℕ) (hpos : Function.Injective pos) (c : Fin m → R) (H : R) (hH : 0 ≤ H)
    (hc : ∀ p, |c p| ≤ H) (e : ℕ) :
    |(wordPoly w u * kernelPoly pos c).coeff e| ≤ H * ∑ i, u i := by
  rw [lin_expand, finset_sum_coeff]
  simp only [coeff_monomial]
  calc |∑ t : Fin n × Fin m, if w t.1 + pos t.2 = e then u t.1 * c t.2 else 0|
      ≤ ∑ t : Fin n × Fin m, |if w t.1 + pos t.2 = e then u t.1 * c t.2 else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ p, (if w i + pos p = e then u i * |c p| else 0) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p _ => ?_))
        split_ifs
        · rw [abs_mul, abs_of_nonneg (hu i)]
        · exact abs_zero
    _ ≤ ∑ i, u i * H := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        apply sum_ite_le_of_unique _ _ _ (mul_nonneg (hu i) hH)
        · intro p
          exact mul_le_mul_of_nonneg_left (hc p) (hu i)
        · intro p q hp hq
          apply hpos
          omega
    _ = H * ∑ i, u i := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)

theorem abs_coeff_const_le {m : ℕ} (pos : Fin m → ℕ) (hpos : Function.Injective pos)
    (c : Fin m → R) (H : R) (hH : 0 ≤ H) (hc : ∀ p, |c p| ≤ H) (e : ℕ) :
    |(kernelPoly pos c).coeff e| ≤ H := by
  rw [kernelPoly, finset_sum_coeff]
  simp only [coeff_monomial]
  calc |∑ p, if pos p = e then c p else 0| ≤ ∑ p, |if pos p = e then c p else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p, (if pos p = e then |c p| else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        split_ifs
        · rfl
        · exact abs_zero
    _ ≤ H := by
        apply sum_ite_le_of_unique _ _ _ hH hc
        intro p q hp hq
        exact hpos (hp.trans hq.symm)

end Order

end Nine121.SparseExtraction
