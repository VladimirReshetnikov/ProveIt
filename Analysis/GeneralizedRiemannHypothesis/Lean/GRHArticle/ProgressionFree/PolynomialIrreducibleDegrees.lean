import GRHArticle.ProgressionFree.PolynomialSmoothSeries
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Squarefree.Basic

/-!
# The finite-field irreducible counts used in the search cutoff

The monic irreducible divisors of `X^(q^n)-X` are exactly those whose
degrees divide `n`. Each occurs once. Taking degrees gives the article's
integer recurrence for `I_q(d)`.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The number `I_q(d)` of monic irreducibles of exact degree `d`. -/
noncomputable def polynomialIrreducibleCount (F : Type*) [Field F] [Fintype F] (d : ℕ) : ℕ :=
  ((polynomialSmoothPrimes F d).filter fun p ↦ p.natDegree = d).card

theorem irreducible_dvd_frobenius_iff {f : Polynomial F} (hi : Irreducible f) (n : ℕ) :
    f ∣ X ^ (Fintype.card F)^n - X ↔ f.natDegree ∣ n := by
  constructor
  · rw [Fintype.card_eq_nat_card]
    exact hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
  · rintro ⟨k, rfl⟩
    letI : Fact (Irreducible f) := ⟨hi⟩
    let e := (AdjoinRoot.powerBasis hi.ne_zero).basis.equivFun
    letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ e.toEquiv.symm
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card F ^ f.natDegree := by
      simpa [Fintype.card_fun, AdjoinRoot.powerBasis_dim] using Fintype.card_congr e.toEquiv
    apply AdjoinRoot.mk_eq_zero.mp
    rw [map_sub, map_pow, pow_mul, ← hcard, FiniteField.pow_card_pow, sub_self]

/-- Summing `d I_q(d)` over the divisors of a positive integer gives `q^n`. -/
theorem sum_divisors_mul_polynomialIrreducibleCount (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, d * polynomialIrreducibleCount F d = Fintype.card F ^ n := by
  classical
  let U : Polynomial F := X ^ Fintype.card F ^ n - X
  have hU : U ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero F hn.ne' Fintype.one_lt_card
  have hdegree : U.natDegree = Fintype.card F ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq F hn.ne' Fintype.one_lt_card
  obtain ⟨e, _, hq⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F ∣ Fintype.card F ^ n :=
    (hq ▸ dvd_pow_self _ e.ne_zero).trans (dvd_pow_self _ hn.ne')
  have hnodup : (normalizedFactors U).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hU).mp (galois_poly_separable _ _ hchar).squarefree
  let S := (normalizedFactors U).toFinset
  have hmem (p : Polynomial F) : p ∈ S ↔ Irreducible p ∧ p.Monic ∧ p.natDegree ∣ n := by
    simp only [S, Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hU]
    exact and_congr_right fun hp ↦ and_congr_right fun _ ↦ irreducible_dvd_frobenius_iff hp n
  have hsum : ∑ p ∈ S, p.natDegree = Fintype.card F ^ n := by
    have hprod := Polynomial.leadingCoeff_mul_prod_normalizedFactors U
    have hdeg := congrArg natDegree hprod
    rw [natDegree_mul (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hU))
      (Multiset.prod_ne_zero (zero_notMem_normalizedFactors U)), natDegree_C, zero_add,
      natDegree_multiset_prod_of_monic, hdegree] at hdeg
    · change (S.val.map natDegree).sum = _
      simpa only [S, Multiset.toFinset_val, hnodup.dedup] using hdeg
    · intro p hp
      exact ((Polynomial.mem_normalizedFactors_iff hU).mp hp).2.1
  rw [← hsum, ← Finset.sum_fiberwise_of_maps_to (g := Polynomial.natDegree)
    (fun p hp ↦ Nat.mem_divisors.mpr ⟨((hmem p).mp hp).2.2, hn.ne'⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  have he : S.filter (fun p ↦ p.natDegree = d) =
      (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d) := by
    ext p
    simp only [Finset.mem_filter, hmem, mem_polynomialSmoothPrimes]
    exact ⟨fun ⟨⟨hi, hm, _⟩, h⟩ ↦ ⟨⟨hm, hi, h.le⟩, h⟩,
      fun ⟨⟨hm, hi, _⟩, h⟩ ↦ ⟨⟨hi, hm, h ▸ hdvd⟩, h⟩⟩
  calc
    d * polynomialIrreducibleCount F d = ∑ _p ∈ S.filter (fun p ↦ p.natDegree = d), d := by
      simp [he, polynomialIrreducibleCount, Nat.mul_comm]
    _ = _ := Finset.sum_congr rfl (fun _ hp ↦ (Finset.mem_filter.mp hp).2.symm)

theorem degree_mul_polynomialIrreducibleCount_le (d : ℕ) (hd : 0 < d) :
    d * polynomialIrreducibleCount F d ≤ Fintype.card F ^ d := by
  rw [← sum_divisors_mul_polynomialIrreducibleCount d hd]
  exact Finset.single_le_sum (f := fun e ↦ e * polynomialIrreducibleCount F e) (fun _ _ ↦ Nat.zero_le _) (Nat.mem_divisors_self _ hd.ne')

end GRHArticle.ProgressionFree
