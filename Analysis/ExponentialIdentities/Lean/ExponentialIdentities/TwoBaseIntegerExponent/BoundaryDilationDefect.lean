import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Boundary dilation defects for rectangular interpolation grids

This file isolates the polynomial algebra behind the boundary-compression
argument.  It is deliberately independent of the analytic construction of an
interpolating polynomial: the interpolation values and distinctness of the
nodes are explicit hypotheses.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Polynomial

section Basic

variable {F : Type*} [Field F]

/-- Substitute `c * X` into a polynomial. -/
noncomputable def polynomialDilation (c : F) (P : F[X]) : F[X] :=
  P.comp (C c * X)

@[simp]
theorem polynomialDilation_eval (c x : F) (P : F[X]) :
    (polynomialDilation c P).eval x = P.eval (c * x) := by
  simp [polynomialDilation]

theorem polynomialDilation_mul (c : F) (P Q : F[X]) :
    polynomialDilation c (P * Q) =
      polynomialDilation c P * polynomialDilation c Q := by
  simp [polynomialDilation, Polynomial.mul_comp]

/-- The defect of `P` under dilation by `c`, relative to the multiplier `m`. -/
noncomputable def dilationDefect (c m : F) (P : F[X]) : F[X] :=
  polynomialDilation c P - C m * P

@[simp]
theorem dilationDefect_eval (c m x : F) (P : F[X]) :
    (dilationDefect c m P).eval x = P.eval (c * x) - m * P.eval x := by
  simp [dilationDefect]

/-- Dilation defects commute, including their scalar correction terms. -/
theorem dilationDefect_commute (c d m n : F) (P : F[X]) :
    dilationDefect c m (dilationDefect d n P) =
      dilationDefect d n (dilationDefect c m P) := by
  simp only [dilationDefect, polynomialDilation, sub_comp, mul_comp, C_comp,
    X_comp, comp_assoc]
  ring_nf

/-- The product of the linear factors at the rectangular nodes
`s^i * t^j`, `0 <= i < a`, `0 <= j < b`. -/
noncomputable def rectangularNodePolynomial (s t : F) (a b : ℕ) : F[X] :=
  ∏ i ∈ Finset.range a, ∏ j ∈ Finset.range b, (X - C (s ^ i * t ^ j))

@[simp]
theorem rectangularNodePolynomial_zero_left (s t : F) (b : ℕ) :
    rectangularNodePolynomial s t 0 b = 1 := by
  simp [rectangularNodePolynomial]

@[simp]
theorem rectangularNodePolynomial_zero_right (s t : F) (a : ℕ) :
    rectangularNodePolynomial s t a 0 = 1 := by
  simp [rectangularNodePolynomial]

@[simp]
theorem rectangularNodePolynomial_eval (s t x : F) (a b : ℕ) :
    (rectangularNodePolynomial s t a b).eval x =
      ∏ i ∈ Finset.range a, ∏ j ∈ Finset.range b, (x - s ^ i * t ^ j) := by
  simp only [rectangularNodePolynomial, eval_prod, eval_sub, eval_X, eval_C]

/-- The top horizontal boundary of an `a` by `b+1` rectangle. -/
noncomputable def upperHorizontalBoundary (s t : F) (a b : ℕ) : F[X] :=
  ∏ i ∈ Finset.range a, (X - C (s ^ i * t ^ b))

/-- The preimage of the bottom horizontal boundary under dilation by `t`. -/
noncomputable def lowerHorizontalBoundary (s t : F) (a : ℕ) : F[X] :=
  ∏ i ∈ Finset.range a, (X - C (s ^ i / t))

/-- The right vertical boundary of an `a+1` by `b` rectangle. -/
noncomputable def upperVerticalBoundary (s t : F) (a b : ℕ) : F[X] :=
  ∏ j ∈ Finset.range b, (X - C (s ^ a * t ^ j))

/-- The preimage of the left vertical boundary under dilation by `s`. -/
noncomputable def lowerVerticalBoundary (s t : F) (b : ℕ) : F[X] :=
  ∏ j ∈ Finset.range b, (X - C (t ^ j / s))

/-- Splitting off the top horizontal boundary of a rectangular node product. -/
theorem rectangularNodePolynomial_succ_right (s t : F) (a b : ℕ) :
    rectangularNodePolynomial s t a (b + 1) =
      rectangularNodePolynomial s t a b * upperHorizontalBoundary s t a b := by
  simp only [rectangularNodePolynomial, upperHorizontalBoundary, Finset.prod_range_succ]
  simp_rw [Finset.prod_mul_distrib]

/-- Splitting off the right vertical boundary of a rectangular node product. -/
theorem rectangularNodePolynomial_succ_left (s t : F) (a b : ℕ) :
    rectangularNodePolynomial s t (a + 1) b =
      rectangularNodePolynomial s t a b * upperVerticalBoundary s t a b := by
  simp [rectangularNodePolynomial, upperVerticalBoundary, Finset.prod_range_succ]

@[simp]
theorem upperHorizontalBoundary_natDegree (s t : F) (a b : ℕ) :
    (upperHorizontalBoundary s t a b).natDegree = a := by
  rw [upperHorizontalBoundary,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

@[simp]
theorem lowerHorizontalBoundary_natDegree (s t : F) (a : ℕ) :
    (lowerHorizontalBoundary s t a).natDegree = a := by
  rw [lowerHorizontalBoundary,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

@[simp]
theorem upperVerticalBoundary_natDegree (s t : F) (a b : ℕ) :
    (upperVerticalBoundary s t a b).natDegree = b := by
  rw [upperVerticalBoundary,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

@[simp]
theorem lowerVerticalBoundary_natDegree (s t : F) (b : ℕ) :
    (lowerVerticalBoundary s t b).natDegree = b := by
  rw [lowerVerticalBoundary,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

end Basic

section Scaling

variable {F : Type*} [Field F] [Infinite F]

omit [Infinite F] in
private theorem horizontalScalarProduct_dilation
    (t u x : F) (b : ℕ) (ht : t ≠ 0) :
    (∏ j ∈ Finset.range (b + 1), (t * x - u * t ^ j)) =
      t ^ (b + 1) * (x - u / t) *
        ∏ j ∈ Finset.range b, (x - u * t ^ j) := by
  induction b with
  | zero =>
      simp
      field_simp
  | succ b ih =>
      rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
      rw [show t * x - u * t ^ (b + 1) = t * (x - u * t ^ b) by
        rw [pow_succ]
        ring]
      rw [pow_succ]
      ring

omit [Infinite F] in
private theorem verticalScalarProduct_dilation
    (s u x : F) (a : ℕ) (hs : s ≠ 0) :
    (∏ i ∈ Finset.range (a + 1), (s * x - s ^ i * u)) =
      s ^ (a + 1) * (x - u / s) *
        ∏ i ∈ Finset.range a, (x - s ^ i * u) := by
  induction a with
  | zero =>
      simp
      field_simp
  | succ a ih =>
      rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
      rw [show s * x - s ^ (a + 1) * u = s * (x - s ^ a * u) by
        rw [pow_succ]
        ring]
      rw [pow_succ]
      ring

/-- Scaling an `a` by `b+1` node rectangle by its vertical base exposes the
interior rectangle and the preimage of the bottom boundary. -/
theorem rectangularNodePolynomial_dilate_vertical
    (s t : F) (a b : ℕ) (ht : t ≠ 0) :
    polynomialDilation t (rectangularNodePolynomial s t a (b + 1)) =
      C (t ^ (a * (b + 1))) * rectangularNodePolynomial s t a b *
        lowerHorizontalBoundary s t a := by
  apply Polynomial.funext
  intro x
  rw [polynomialDilation_eval, rectangularNodePolynomial_eval]
  simp_rw [horizontalScalarProduct_dilation (b := b) (ht := ht)]
  simp only [eval_mul, eval_C, rectangularNodePolynomial_eval,
    lowerHorizontalBoundary, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [pow_mul]
  ring

/-- Scaling an `a+1` by `b` node rectangle by its horizontal base exposes the
interior rectangle and the preimage of the left boundary. -/
theorem rectangularNodePolynomial_dilate_horizontal
    (s t : F) (a b : ℕ) (hs : s ≠ 0) :
    polynomialDilation s (rectangularNodePolynomial s t (a + 1) b) =
      C (s ^ ((a + 1) * b)) * rectangularNodePolynomial s t a b *
        lowerVerticalBoundary s t b := by
  apply Polynomial.funext
  intro x
  rw [polynomialDilation_eval, rectangularNodePolynomial_eval]
  rw [Finset.prod_comm]
  simp only [eval_mul, eval_C, rectangularNodePolynomial_eval,
    lowerVerticalBoundary, eval_prod, eval_sub, eval_X, eval_C]
  simp_rw [verticalScalarProduct_dilation (a := a) (hs := hs)]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [pow_mul]
  rw [show (∏ j ∈ Finset.range b, ∏ i ∈ Finset.range a,
      (x - s ^ i * t ^ j)) =
      ∏ i ∈ Finset.range a, ∏ j ∈ Finset.range b,
        (x - s ^ i * t ^ j) by exact Finset.prod_comm]
  ring

end Scaling

section RootsAndInterpolation

variable {F : Type*} [Field F]

theorem rectangularNodePolynomial_monic (s t : F) (a b : ℕ) :
    (rectangularNodePolynomial s t a b).Monic := by
  rw [rectangularNodePolynomial, ← Finset.prod_product']
  exact Polynomial.monic_prod_X_sub_C
    (fun ij : ℕ × ℕ ↦ s ^ ij.1 * t ^ ij.2)
    (Finset.range a ×ˢ Finset.range b)

@[simp]
theorem rectangularNodePolynomial_natDegree (s t : F) (a b : ℕ) :
    (rectangularNodePolynomial s t a b).natDegree = a * b := by
  rw [rectangularNodePolynomial, ← Finset.prod_product',
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

theorem rectangularNodePolynomial_ne_zero (s t : F) (a b : ℕ) :
    rectangularNodePolynomial s t a b ≠ 0 :=
  (rectangularNodePolynomial_monic s t a b).ne_zero

/-- Distinct rectangular nodes that are all roots of `P` supply their full
squarefree node product as a divisor of `P`. -/
theorem rectangularNodePolynomial_dvd_of_eval_zero
    (s t : F) (a b : ℕ) (P : F[X])
    (hinj : ∀ {i j i' j' : ℕ}, i < a → j < b → i' < a → j' < b →
      s ^ i * t ^ j = s ^ i' * t ^ j' → i = i' ∧ j = j')
    (hzero : ∀ i < a, ∀ j < b, P.eval (s ^ i * t ^ j) = 0) :
    rectangularNodePolynomial s t a b ∣ P := by
  classical
  rw [rectangularNodePolynomial, ← Finset.prod_product']
  apply Finset.prod_dvd_of_coprime
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' hpairs
    have hij0 : i < a ∧ j < b := by simpa using hij
    have hij0' : i' < a ∧ j' < b := by simpa using hij'
    have hnodes : s ^ i * t ^ j ≠ s ^ i' * t ^ j' := by
      intro h
      have hindices := hinj hij0.1 hij0.2 hij0'.1 hij0'.2 h
      exact hpairs (Prod.ext hindices.1 hindices.2)
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero_of_ne hnodes).isUnit
  · rintro ⟨i, j⟩ hij
    have hij0 : i < a ∧ j < b := by simpa using hij
    rw [Polynomial.dvd_iff_isRoot]
    exact hzero i hij0.1 j hij0.2

/-- Interpolation on an `(a+1)` by `b` multiplicative rectangle makes the
horizontal dilation defect vanish on the `a` by `b` interior rectangle. -/
theorem rectangularNodePolynomial_dvd_horizontalDefect
    (s t m n : F) (a b : ℕ) (Q : F[X])
    (hinj : ∀ {i j i' j' : ℕ}, i < a → j < b → i' < a → j' < b →
      s ^ i * t ^ j = s ^ i' * t ^ j' → i = i' ∧ j = j')
    (hQ : ∀ i < a + 1, ∀ j < b,
      Q.eval (s ^ i * t ^ j) = m ^ i * n ^ j) :
    rectangularNodePolynomial s t a b ∣ dilationDefect s m Q := by
  apply rectangularNodePolynomial_dvd_of_eval_zero s t a b _ hinj
  intro i hi j hj
  rw [dilationDefect_eval]
  have hnode : s * (s ^ i * t ^ j) = s ^ (i + 1) * t ^ j := by
    rw [pow_succ]
    ring
  rw [hnode, hQ (i + 1) (by omega) j hj, hQ i (by omega) j hj, pow_succ]
  ring

/-- Interpolation on an `a` by `(b+1)` multiplicative rectangle makes the
vertical dilation defect vanish on the `a` by `b` interior rectangle. -/
theorem rectangularNodePolynomial_dvd_verticalDefect
    (s t m n : F) (a b : ℕ) (Q : F[X])
    (hinj : ∀ {i j i' j' : ℕ}, i < a → j < b → i' < a → j' < b →
      s ^ i * t ^ j = s ^ i' * t ^ j' → i = i' ∧ j = j')
    (hQ : ∀ i < a, ∀ j < b + 1,
      Q.eval (s ^ i * t ^ j) = m ^ i * n ^ j) :
    rectangularNodePolynomial s t a b ∣ dilationDefect t n Q := by
  apply rectangularNodePolynomial_dvd_of_eval_zero s t a b _ hinj
  intro i hi j hj
  rw [dilationDefect_eval]
  have hnode : t * (s ^ i * t ^ j) = s ^ i * t ^ (j + 1) := by
    rw [pow_succ]
    ring
  rw [hnode, hQ i hi (j + 1) (by omega), hQ i hi j (by omega), pow_succ]
  ring

end RootsAndInterpolation

section ResidualDegree

variable {F : Type*} [Field F]

theorem polynomialDilation_natDegree (c : F) (P : F[X]) (hc : c ≠ 0) :
    (polynomialDilation c P).natDegree = P.natDegree := by
  rw [polynomialDilation, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X, mul_one]

theorem polynomialDilation_leadingCoeff (c : F) (P : F[X]) (hc : c ≠ 0) :
    (polynomialDilation c P).leadingCoeff = P.leadingCoeff * c ^ P.natDegree := by
  have hinner : (C c * X : F[X]).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X]
    norm_num
  rw [polynomialDilation, Polynomial.leadingCoeff_comp hinner,
    (Polynomial.monic_X : (X : F[X]).Monic).leadingCoeff_C_mul]

theorem dilationDefect_coeff_natDegree (c m : F) (P : F[X]) (hc : c ≠ 0) :
    (dilationDefect c m P).coeff P.natDegree =
      P.leadingCoeff * (c ^ P.natDegree - m) := by
  have hdeg := polynomialDilation_natDegree c P hc
  calc
    (dilationDefect c m P).coeff P.natDegree =
        (polynomialDilation c P).coeff P.natDegree -
          m * P.coeff P.natDegree := by
            simp only [dilationDefect, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    _ = (polynomialDilation c P).leadingCoeff - m * P.leadingCoeff := by
          have hdilcoeff : (polynomialDilation c P).coeff P.natDegree =
              (polynomialDilation c P).leadingCoeff := by
            rw [← hdeg, Polynomial.coeff_natDegree]
          rw [hdilcoeff, Polynomial.coeff_natDegree]
    _ = P.leadingCoeff * (c ^ P.natDegree - m) := by
          rw [polynomialDilation_leadingCoeff c P hc]
          ring

/-- A nonzero top dilation multiplier prevents leading-term cancellation in
the defect, so the defect retains the degree of the original polynomial. -/
theorem dilationDefect_natDegree (c m : F) (P : F[X]) (hc : c ≠ 0)
    (hP : P ≠ 0) (hscale : c ^ P.natDegree - m ≠ 0) :
    (dilationDefect c m P).natDegree = P.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine (Polynomial.natDegree_sub_le _ _).trans ?_
    apply max_le
    · exact (polynomialDilation_natDegree c P hc).le
    · exact Polynomial.natDegree_C_mul_le m P
  · rw [dilationDefect_coeff_natDegree c m P hc]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) hscale

theorem dilationDefect_leadingCoeff (c m : F) (P : F[X]) (hc : c ≠ 0)
    (hP : P ≠ 0) (hscale : c ^ P.natDegree - m ≠ 0) :
    (dilationDefect c m P).leadingCoeff =
      P.leadingCoeff * (c ^ P.natDegree - m) := by
  rw [Polynomial.leadingCoeff, dilationDefect_natDegree c m P hc hP hscale,
    dilationDefect_coeff_natDegree c m P hc]

/-- A divisible dilation defect has a unique residual polynomial.  Its degree
and leading coefficient are exact whenever the original leading term does not
cancel.  The equation `natDegree Q = a*b+r` makes the degree subtraction
explicit without truncated natural-number arithmetic. -/
theorem existsUnique_dilationResidual
    (s t c m : F) (a b r : ℕ) (Q : F[X])
    (hc : c ≠ 0) (hQ0 : Q ≠ 0)
    (hQdeg : Q.natDegree = a * b + r)
    (hscale : c ^ Q.natDegree - m ≠ 0)
    (hdiv : rectangularNodePolynomial s t a b ∣ dilationDefect c m Q) :
    ∃! U : F[X],
      dilationDefect c m Q = rectangularNodePolynomial s t a b * U ∧
      U.natDegree = r ∧
      U.leadingCoeff = Q.leadingCoeff * (c ^ Q.natDegree - m) := by
  obtain ⟨U, hU⟩ := hdiv
  have hD0 : dilationDefect c m Q ≠ 0 := by
    exact Polynomial.leadingCoeff_ne_zero.mp
      (dilationDefect_leadingCoeff c m Q hc hQ0 hscale |>.trans_ne
        (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ0) hscale))
  have hPi0 := rectangularNodePolynomial_ne_zero s t a b
  have hU0 : U ≠ 0 := by
    intro h
    rw [h] at hU
    simp only [mul_zero] at hU
    exact hD0 hU
  have hUdeg : U.natDegree = r := by
    have hmuldeg := Polynomial.natDegree_mul hPi0 hU0
    rw [← hU, dilationDefect_natDegree c m Q hc hQ0 hscale,
      rectangularNodePolynomial_natDegree, hQdeg] at hmuldeg
    omega
  have hUlead : U.leadingCoeff =
      Q.leadingCoeff * (c ^ Q.natDegree - m) := by
    have hlead := congrArg Polynomial.leadingCoeff hU
    rw [Polynomial.leadingCoeff_mul,
      (rectangularNodePolynomial_monic s t a b).leadingCoeff, one_mul,
      dilationDefect_leadingCoeff c m Q hc hQ0 hscale] at hlead
    exact hlead.symm
  refine ⟨U, ⟨hU, hUdeg, hUlead⟩, ?_⟩
  intro V hV
  apply mul_left_cancel₀ hPi0
  rw [← hU, ← hV.1]

/-- **Exact square-grid dilation-defect factorization.**  An interpolant on a
`K` by `K` multiplicative grid has unique horizontal and vertical residuals of
degree `K-1`, provided the nodes are distinct, the interpolant has full degree,
and its leading term does not cancel under either dilation. -/
theorem existsUnique_squareGridResiduals
    (s t m n : F) (K : ℕ) (Q : F[X])
    (hK : 2 ≤ K) (hs : s ≠ 0) (ht : t ≠ 0) (hQ0 : Q ≠ 0)
    (hinj : ∀ {i j i' j' : ℕ}, i < K → j < K → i' < K → j' < K →
      s ^ i * t ^ j = s ^ i' * t ^ j' → i = i' ∧ j = j')
    (hQ : ∀ i < K, ∀ j < K,
      Q.eval (s ^ i * t ^ j) = m ^ i * n ^ j)
    (hQdeg : Q.natDegree = K * K - 1)
    (hscaleS : s ^ Q.natDegree - m ≠ 0)
    (hscaleT : t ^ Q.natDegree - n ≠ 0) :
    (∃! U : F[X],
      dilationDefect s m Q =
          rectangularNodePolynomial s t (K - 1) K * U ∧
      U.natDegree = K - 1 ∧
      U.leadingCoeff = Q.leadingCoeff * (s ^ Q.natDegree - m)) ∧
    (∃! V : F[X],
      dilationDefect t n Q =
          rectangularNodePolynomial s t K (K - 1) * V ∧
      V.natDegree = K - 1 ∧
      V.leadingCoeff = Q.leadingCoeff * (t ^ Q.natDegree - n)) := by
  have hpred : K - 1 + 1 = K := by omega
  have hdegHorizontal : Q.natDegree = (K - 1) * K + (K - 1) := by
    rw [hQdeg]
    calc
      K * K - 1 = K * ((K - 1) + 1) - 1 := by rw [hpred]
      _ = (K * (K - 1) + K) - 1 := by rw [mul_add, mul_one]
      _ = K * (K - 1) + (K - 1) := by omega
      _ = (K - 1) * K + (K - 1) := by rw [mul_comm K (K - 1)]
  have hdegVertical : Q.natDegree = K * (K - 1) + (K - 1) := by
    rw [hQdeg]
    calc
      K * K - 1 = K * ((K - 1) + 1) - 1 := by rw [hpred]
      _ = (K * (K - 1) + K) - 1 := by rw [mul_add, mul_one]
      _ = K * (K - 1) + (K - 1) := by omega
  have hdivU : rectangularNodePolynomial s t (K - 1) K ∣
      dilationDefect s m Q := by
    apply rectangularNodePolynomial_dvd_horizontalDefect
      s t m n (K - 1) K Q
    · intro i j i' j' hi hj hi' hj' heq
      exact hinj (by omega) hj (by omega) hj' heq
    · intro i hi j hj
      exact hQ i (by omega) j hj
  have hdivV : rectangularNodePolynomial s t K (K - 1) ∣
      dilationDefect t n Q := by
    apply rectangularNodePolynomial_dvd_verticalDefect
      s t m n K (K - 1) Q
    · intro i j i' j' hi hj hi' hj' heq
      exact hinj hi (by omega) hi' (by omega) heq
    · intro i hi j hj
      exact hQ i hi j (by omega)
  constructor
  · exact existsUnique_dilationResidual s t s m (K - 1) K (K - 1) Q
      hs hQ0 hdegHorizontal hscaleS hdivU
  · exact existsUnique_dilationResidual s t t n K (K - 1) (K - 1) Q
      ht hQ0 hdegVertical hscaleT hdivV

end ResidualDegree

section BoundaryCommutator

variable {F : Type*} [Field F]

private theorem natDegree_C_mul_mul_le (z : F) (P R : F[X]) :
    (C z * P * R).natDegree ≤ P.natDegree + R.natDegree := by
  calc
    (C z * P * R).natDegree ≤ (C z * P).natDegree + R.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (C z).natDegree + P.natDegree + R.natDegree := by
      gcongr
      exact Polynomial.natDegree_mul_le
    _ = P.natDegree + R.natDegree := by simp

/-- The horizontal boundary side has degree at most the sum of the boundary
length and the residual degree. -/
theorem horizontalBoundaryExpression_natDegree_le
    (s t n : F) (a b r : ℕ) (U : F[X]) (ht : t ≠ 0)
    (hU : U.natDegree ≤ r) :
    (C (t ^ (a * (b + 1))) * lowerHorizontalBoundary s t a *
          polynomialDilation t U -
        C n * upperHorizontalBoundary s t a b * U).natDegree ≤ a + r := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_C_mul_mul_le _ _ _).trans ?_
    rw [lowerHorizontalBoundary_natDegree,
      polynomialDilation_natDegree t U ht]
    omega
  · refine (natDegree_C_mul_mul_le _ _ _).trans ?_
    rw [upperHorizontalBoundary_natDegree]
    omega

/-- The vertical boundary side has degree at most the sum of the boundary
length and the residual degree. -/
theorem verticalBoundaryExpression_natDegree_le
    (s t m : F) (a b r : ℕ) (V : F[X]) (hs : s ≠ 0)
    (hV : V.natDegree ≤ r) :
    (C (s ^ ((a + 1) * b)) * lowerVerticalBoundary s t b *
          polynomialDilation s V -
        C m * upperVerticalBoundary s t a b * V).natDegree ≤ b + r := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_C_mul_mul_le _ _ _).trans ?_
    rw [lowerVerticalBoundary_natDegree,
      polynomialDilation_natDegree s V hs]
    omega
  · refine (natDegree_C_mul_mul_le _ _ _).trans ?_
    rw [upperVerticalBoundary_natDegree]
    omega

/-- On the square boundary with residual degree `K-1`, each commutator side
has the report's bound `2*K-2`. -/
theorem squareBoundaryExpressions_natDegree_le
    (s t m n : F) (K : ℕ) (U V : F[X])
    (hs : s ≠ 0) (ht : t ≠ 0) (hK : 1 ≤ K)
    (hU : U.natDegree = K - 1) (hV : V.natDegree = K - 1) :
    (C (t ^ ((K - 1) * ((K - 1) + 1))) *
          lowerHorizontalBoundary s t (K - 1) * polynomialDilation t U -
        C n * upperHorizontalBoundary s t (K - 1) (K - 1) * U).natDegree
        ≤ 2 * K - 2 ∧
    (C (s ^ (((K - 1) + 1) * (K - 1))) *
          lowerVerticalBoundary s t (K - 1) * polynomialDilation s V -
        C m * upperVerticalBoundary s t (K - 1) (K - 1) * V).natDegree
        ≤ 2 * K - 2 := by
  constructor
  · have h := horizontalBoundaryExpression_natDegree_le
      s t n (K - 1) (K - 1) (K - 1) U ht hU.le
    omega
  · have h := verticalBoundaryExpression_natDegree_le
      s t m (K - 1) (K - 1) (K - 1) V hs hV.le
    omega

variable [Infinite F]

/-- Cancelling the common interior node polynomial from commuting horizontal
and vertical dilation defects leaves a boundary identity.  For
`a = b = K-1`, this is precisely the report's degree-`2K-2` commutator. -/
theorem boundaryDilation_commutator
    (s t m n : F) (a b : ℕ) (Q U V : F[X])
    (hs : s ≠ 0) (ht : t ≠ 0)
    (hU : dilationDefect s m Q =
      rectangularNodePolynomial s t a (b + 1) * U)
    (hV : dilationDefect t n Q =
      rectangularNodePolynomial s t (a + 1) b * V) :
    C (t ^ (a * (b + 1))) * lowerHorizontalBoundary s t a *
          polynomialDilation t U -
        C n * upperHorizontalBoundary s t a b * U =
      C (s ^ ((a + 1) * b)) * lowerVerticalBoundary s t b *
          polynomialDilation s V -
        C m * upperVerticalBoundary s t a b * V := by
  have hcomm := dilationDefect_commute s t m n Q
  rw [hV, hU] at hcomm
  simp only [dilationDefect, polynomialDilation_mul] at hcomm
  rw [rectangularNodePolynomial_dilate_horizontal s t a b hs,
    rectangularNodePolynomial_dilate_vertical s t a b ht,
    rectangularNodePolynomial_succ_left,
    rectangularNodePolynomial_succ_right] at hcomm
  apply mul_left_cancel₀ (rectangularNodePolynomial_ne_zero s t a b)
  linear_combination -hcomm

end BoundaryCommutator

end LeanProofs.TwoBaseIntegerExponent
