import Surreal.Algebra.PolynomialResultant
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-!
# The native polynomial discriminant

This file proves the pairwise squared-root product, signed resultant identity,
and repeated-root criterion
in `polynomial:eq:discdef` of
`docs/surcomplex/polynomial-algebra/article.tex`, using Mathlib's
`Polynomial.discr` without introducing another discriminant.

Mathlib assigns discriminant one to every constant polynomial, including
zero, and to every linear polynomial. The general leading-coefficient
relation therefore requires positive degree. The monic identity also holds
in degree zero, where the polynomial is one. Characteristic zero identifies
the actual derivative degree with the size `n - 1` used by the native
Sylvester derivative identity.
-/

namespace Surreal.FinitePolynomial

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- Native constant convention; the source's leading-coefficient formula
is used only in positive degree. -/
theorem discr_constant (a : R) : (C a).discr = 1 := Polynomial.discr_C a

/-- The empty pair product for a linear polynomial is one. -/
theorem discr_linear (P : R[X]) (hP : P.degree = 1) : P.discr = 1 :=
  Polynomial.discr_of_degree_eq_one hP

end CommRing

private theorem prod_offDiag_sub {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, (a i - a j)) =
      (-1) ^ (n * (n - 1) / 2) * ∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2 := by
  classical
  have hsplit (i : Fin n) : Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    exact ne_iff_lt_or_gt
  have hdisj (i : Fin n) : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    simp only [Finset.disjoint_left, Finset.mem_Iio, Finset.mem_Ioi]
    exact fun j hj hi => (lt_asymm hj hi).elim
  simp_rw [hsplit, Finset.prod_union (hdisj _)]
  rw [Finset.prod_mul_distrib]
  have hflip : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a i - a j)) =
      ∏ i : Fin n, ∏ j ∈ Finset.Iio i, (a j - a i) := by
    exact Finset.prod_comm' (by simp)
  rw [hflip, ← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib]
  have hpair (i j : Fin n) : (a i - a j) * (a j - a i) = (-1) * (a i - a j) ^ 2 := by ring
  simp_rw [hpair, Finset.prod_mul_distrib, Finset.prod_const,
    Fin.card_Iio]
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i : Fin n, (i : ℕ)) = n * (n - 1) / 2 := by
    simpa only [Finset.sum_range_id] using (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n)
  rw [hsum]

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The resultant/discriminant identity with the leading coefficient
retained. Positive degree is essential for nonmonic constants. -/
theorem leadingCoeff_mul_discr_eq_sign_mul_resultant (P : K[X])
    (hP : 0 < P.natDegree) :
    P.leadingCoeff * P.discr =
      (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) * P.resultant P.derivative := by
  have h : P.resultant P.derivative =
      (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) * P.leadingCoeff * P.discr := by
    simpa only [Polynomial.natDegree_derivative] using
      Polynomial.resultant_deriv (natDegree_pos_iff_degree_pos.mp hP)
  rw [h, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- The monic identity in `polynomial:eq:discdef`, including the constant
polynomial one. The resultant uses the actual derivative degree. -/
theorem discr_eq_sign_mul_resultant (P : K[X]) (hP : P.Monic) :
    P.discr = (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      P.resultant P.derivative := by
  by_cases hn : P.natDegree = 0
  · have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP hn
    rw [h1, ← C_1, Polynomial.discr_C]
    simp
  · simpa only [hP.leadingCoeff, one_mul] using
      leadingCoeff_mul_discr_eq_sign_mul_resultant P (Nat.pos_of_ne_zero hn)

/-- For a nonzero polynomial, vanishing of the native discriminant agrees
with vanishing of the derivative resultant, including nonzero constants. -/
theorem discr_eq_zero_iff_resultant_derivative_eq_zero (P : K[X]) (hP : P ≠ 0) :
    P.discr = 0 ↔ P.resultant P.derivative = 0 := by
  by_cases hn : P.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hn]
    simp
  · have h := leadingCoeff_mul_discr_eq_sign_mul_resultant P (Nat.pos_of_ne_zero hn)
    have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
    have hs : (-1 : K) ^ (P.natDegree * (P.natDegree - 1) / 2) ≠ 0 :=
      pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    simpa only [mul_eq_zero, hl, hs, false_or] using (congrArg (· = 0) h).to_iff

/-- The discriminant is nonzero exactly for squarefree nonzero
polynomials. Characteristic zero supplies perfectness. No splitting
assumption is needed for this criterion. -/
theorem discr_ne_zero_iff_squarefree (P : K[X]) (hP : P ≠ 0) :
    P.discr ≠ 0 ↔ Squarefree P := by
  exact (discr_eq_zero_iff_resultant_derivative_eq_zero P hP).not.trans
    ((resultant_ne_zero_iff_isCoprime P P.derivative hP).trans
      PerfectField.separable_iff_squarefree)

/-- Vanishing of the discriminant means that a split nonzero polynomial
has a root of multiplicity at least two, as stated after
`polynomial:eq:discdef`. Repeated roots are counted algebraically. -/
theorem discr_eq_zero_iff_repeated_root (P : K[X]) (hP : P ≠ 0) (hs : P.Splits) :
    P.discr = 0 ↔ ∃ a : K, 1 < P.rootMultiplicity a := by
  rw [discr_eq_zero_iff_resultant_derivative_eq_zero P hP,
    resultant_eq_zero_iff_common_root P P.derivative hP hs]
  exact exists_congr fun _ => (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).symm

/-- The leading-coefficient and pairwise squared-difference formula of
`polynomial:eq:discdef` for an indexed factorization. Indices represent
root occurrences, so distinct indices may contain the same root. Positive
degree avoids interpreting the source's integer exponent `2n - 2` at zero. -/
theorem discr_C_mul_prod_X_sub_C {n : ℕ} (hn : 0 < n) (c : K) (hc : c ≠ 0)
    (a : Fin n → K) :
    (C c * ∏ i, (X - C (a i))).discr =
      c ^ (2 * n - 2) * ∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2 := by
  classical
  let P : K[X] := C c * ∏ i, (X - C (a i))
  have hdegree : P.natDegree = n := by
    simp [P, natDegree_C_mul hc]
  have hlead : P.leadingCoeff = c := by
    dsimp only [P]
    rw [leadingCoeff_mul, leadingCoeff_C,
      (monic_prod_X_sub_C a Finset.univ).leadingCoeff, mul_one]
  have hsplit : P.Splits :=
    (Splits.C c).mul (Splits.prod fun i _ => Splits.X_sub_C (a i))
  have hroots : P.roots = Finset.univ.val.map a := by
    dsimp only [P]
    rw [roots_C_mul _ hc, Finset.prod]
    simpa only [Multiset.map_map, Function.comp_def] using
      roots_multiset_prod_X_sub_C (Finset.univ.val.map a)
  have heval (i : Fin n) : P.derivative.eval (a i) =
      c * ∏ j ∈ Finset.univ.erase i, (a i - a j) := by
    dsimp only [P]
    rw [derivative_C_mul, eval_mul, eval_C,
      ← Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]
    simp [Polynomial.eval_prod]
  have hres : P.resultant P.derivative =
      c ^ (n - 1) * (c ^ n * ∏ i, ∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
    rw [resultant_eq_leadingCoeff_mul_prod_eval P P.derivative hsplit,
      hlead, natDegree_derivative, hdegree, hroots, Multiset.map_map]
    change c ^ (n - 1) * (∏ i, P.derivative.eval (a i)) = _
    simp_rw [heval]
    rw [Finset.prod_mul_distrib]
    simp
  have h := leadingCoeff_mul_discr_eq_sign_mul_resultant P (hdegree ▸ hn)
  rw [hlead, hres, hdegree, prod_offDiag_sub] at h
  have hsign : (-1 : K) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  apply mul_left_cancel₀ hc
  change c * P.discr = _
  rw [h]
  calc
    _ = c ^ (n - 1) * c ^ n *
        ((-1 : K) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 1) / 2)) *
        (∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2) := by ring
    _ = c * (c ^ (2 * n - 2) * ∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2) := by
      rw [hsign, mul_one, ← pow_add, ← mul_assoc, ← pow_succ']
      congr 2
      omega

/-- The source's pair product for a monic polynomial given by its indexed
roots. The degree-zero case is the empty product and has discriminant one. -/
theorem discr_prod_X_sub_C {n : ℕ} (a : Fin n → K) :
    (∏ i, (X - C (a i))).discr =
      ∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2 := by
  cases n with
  | zero => simpa using (Polynomial.discr_C (1 : K))
  | succ n =>
    simpa using discr_C_mul_prod_X_sub_C (Nat.succ_pos n) (1 : K) one_ne_zero a

/-- The full `polynomial:eq:discdef` pair product expressed for an
arbitrary positive-degree polynomial and a chosen enumeration of its roots,
with multiplicities. The enumeration is supplied by a splitting hypothesis
elsewhere; algebraic closedness is not assumed here. -/
theorem discr_eq_leadingCoeff_pow_mul_prod_sub_sq (P : K[X])
    (hP : 0 < P.natDegree) (a : Fin P.natDegree → K)
    (hfactor : P = C P.leadingCoeff * ∏ i, (X - C (a i))) :
    P.discr = P.leadingCoeff ^ (2 * P.natDegree - 2) *
      ∏ i, ∏ j ∈ Finset.Iio i, (a i - a j) ^ 2 := by
  calc
    P.discr = (C P.leadingCoeff * ∏ i, (X - C (a i))).discr := congrArg discr hfactor
    _ = _ := discr_C_mul_prod_X_sub_C hP P.leadingCoeff
      (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hP)) a

end Field

end Surreal.FinitePolynomial
