import ExponentialIdentities.TwoBaseIntegerExponent.BlockVandermondeValuationBudget
import Mathlib.LinearAlgebra.Vandermonde

/-!
# All-layer divisibility from unit-adapted polynomial bases

A monic triangular change from monomials to integer polynomials preserves an
evaluation determinant.  If the new column of degree `j` is pointwise divisible
by `p ^ w j`, this gives a divisor of the *whole determinant*, independently of
which tropical assignment layer contributes.  The concrete unit bases below
give lower-order gains; they do not bound the remaining cancellation cascade.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix Polynomial

/-- If every entry in column `j` is divisible by `q j`, the product of the
column divisors divides the determinant. -/
theorem prod_columnDivisor_dvd_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (q : n → ℤ)
    (hdiv : ∀ i j, q j ∣ A i j) :
    (∏ j : n, q j) ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro sigma _
  apply Dvd.dvd.mul_left
  exact Finset.prod_dvd_prod_of_dvd q (fun j ↦ A (sigma j) j)
    (fun j _ ↦ hdiv (sigma j) j)

/-- Prime-power specialization of `prod_columnDivisor_dvd_det`. -/
theorem pow_sum_columnWeight_dvd_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (p : ℤ) (w : n → ℕ)
    (hdiv : ∀ i j, p ^ w j ∣ A i j) :
    p ^ (∑ j : n, w j) ∣ A.det := by
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ w p]
  exact prod_columnDivisor_dvd_det A (fun j ↦ p ^ w j) hdiv

/-- A unimodular column change may be used before extracting column content. -/
theorem pow_sum_columnWeight_dvd_det_of_unimodular_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℤ) (p : ℤ) (w : n → ℕ)
    (hU : U.det = 1)
    (hdiv : ∀ i j, p ^ w j ∣ (A * U) i j) :
    p ^ (∑ j : n, w j) ∣ A.det := by
  have h := pow_sum_columnWeight_dvd_det (A * U) p w hdiv
  rwa [Matrix.det_mul, hU, mul_one] at h

/-- **Monic-basis all-layer divisor.**  Replacing `X^j` by any monic integer
polynomial of degree `j` preserves the Vandermonde determinant.  Pointwise
fixed divisors of those polynomial values therefore divide the complete
determinant, not merely its first tropical initial form. -/
theorem pow_sum_dvd_det_vandermonde_of_monicBasis
    {n : ℕ} (x : Fin n → ℤ) (P : Fin n → ℤ[X]) (p : ℤ)
    (w : Fin n → ℕ)
    (hdeg : ∀ j, (P j).natDegree = j)
    (hmonic : ∀ j, (P j).Monic)
    (hdiv : ∀ i j, p ^ w j ∣ (P j).eval (x i)) :
    p ^ (∑ j : Fin n, w j) ∣ (Matrix.vandermonde x).det := by
  let B : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j ↦ (P j).eval (x i)
  have hB : p ^ (∑ j : Fin n, w j) ∣ B.det := by
    apply pow_sum_columnWeight_dvd_det B p w
    exact hdiv
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x P hdeg hmonic]
  exact hB

/-- The shifted monomial basis `(X - c)^j`. -/
noncomputable def shiftedPowerBasis {n : ℕ} (c : ℤ) (j : Fin n) : ℤ[X] :=
  (X - C c) ^ (j : ℕ)

theorem shiftedPowerBasis_natDegree {n : ℕ} (c : ℤ) (j : Fin n) :
    (shiftedPowerBasis c j).natDegree = j := by
  rw [shiftedPowerBasis, Polynomial.natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]

theorem shiftedPowerBasis_monic {n : ℕ} (c : ℤ) (j : Fin n) :
    (shiftedPowerBasis c j).Monic :=
  (Polynomial.monic_X_sub_C c).pow _

@[simp]
theorem shiftedPowerBasis_eval {n : ℕ} (c z : ℤ) (j : Fin n) :
    (shiftedPowerBasis c j).eval z = (z - c) ^ (j : ℕ) := by
  simp [shiftedPowerBasis]

/-- **Dyadic unit-column gain.**  If every node is congruent to `1` modulo
`2`, the degree-`j` shifted column contributes `2^j`.  The displayed
complete-determinant divisor is `2 ^ (sum j)`, independent of higher
tropical layers. -/
theorem two_pow_sum_degree_dvd_det_vandermonde_of_odd
    {n : ℕ} (x : Fin n → ℤ)
    (hodd : ∀ i, (2 : ℤ) ∣ x i - 1) :
    (2 : ℤ) ^ (∑ j : Fin n, (j : ℕ)) ∣ (Matrix.vandermonde x).det := by
  apply pow_sum_dvd_det_vandermonde_of_monicBasis x
    (shiftedPowerBasis 1) 2 (fun j ↦ (j : ℕ))
    (shiftedPowerBasis_natDegree 1) (shiftedPowerBasis_monic 1)
  intro i j
  rw [shiftedPowerBasis_eval]
  exact pow_dvd_pow_of_dvd (hodd i) _

/-- A simple triadic unit basis.  Degree `j=2q+r` uses
`X^r * (X^2 - 1)^q`; on a `3`-adic unit the second factor is divisible by
`3^q`. -/
noncomputable def threeUnitPowerBasis {n : ℕ} (j : Fin n) : ℤ[X] :=
  X ^ ((j : ℕ) % 2) * (X ^ 2 - C 1) ^ ((j : ℕ) / 2)

theorem threeUnitPowerBasis_monic {n : ℕ} (j : Fin n) :
    (threeUnitPowerBasis j).Monic :=
  (Polynomial.monic_X_pow _).mul
    ((Polynomial.monic_X_pow_sub_C (1 : ℤ) (by norm_num : 2 ≠ 0)).pow _)

theorem threeUnitPowerBasis_natDegree {n : ℕ} (j : Fin n) :
    (threeUnitPowerBasis j).natDegree = j := by
  rw [threeUnitPowerBasis,
    (Polynomial.monic_X_pow _).natDegree_mul
      ((Polynomial.monic_X_pow_sub_C (1 : ℤ) (by norm_num : 2 ≠ 0)).pow _),
    Polynomial.natDegree_X_pow, Polynomial.natDegree_pow,
    Polynomial.natDegree_X_pow_sub_C]
  omega

@[simp]
theorem threeUnitPowerBasis_eval {n : ℕ} (z : ℤ) (j : Fin n) :
    (threeUnitPowerBasis j).eval z =
      z ^ ((j : ℕ) % 2) * (z ^ 2 - 1) ^ ((j : ℕ) / 2) := by
  simp [threeUnitPowerBasis]

theorem three_dvd_sq_sub_one_of_not_dvd (z : ℤ) (hz : ¬ (3 : ℤ) ∣ z) :
    (3 : ℤ) ∣ z ^ 2 - 1 := by
  have hr_nonneg : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
  have hr_lt : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
  have hr_ne : z % 3 ≠ 0 := by
    simpa only [Int.dvd_iff_emod_eq_zero] using hz
  have hr : z % 3 = 1 ∨ z % 3 = 2 := by omega
  let q := z / 3
  have hzdecomp : q * 3 + z % 3 = z := Int.ediv_mul_add_emod z 3
  rcases hr with hr | hr
  · refine ⟨3 * q ^ 2 + 2 * q, ?_⟩
    rw [← hzdecomp, hr]
    ring
  · refine ⟨3 * q ^ 2 + 4 * q + 1, ?_⟩
    rw [← hzdecomp, hr]
    ring

/-- **Triadic unit-column gain.**  For nodes prime to `3`, the complete
Vandermonde determinant gains the displayed divisor coming from the weights
`floor(j/2)` of the simple unit basis.  This gain is lower-order in the
mixed-block application and makes no assertion about the remaining cascade. -/
theorem three_pow_sum_halfDegree_dvd_det_vandermonde_of_unit
    {n : ℕ} (x : Fin n → ℤ)
    (hunit : ∀ i, ¬ (3 : ℤ) ∣ x i) :
    (3 : ℤ) ^ (∑ j : Fin n, (j : ℕ) / 2) ∣ (Matrix.vandermonde x).det := by
  apply pow_sum_dvd_det_vandermonde_of_monicBasis x
    threeUnitPowerBasis 3 (fun j ↦ (j : ℕ) / 2)
    threeUnitPowerBasis_natDegree threeUnitPowerBasis_monic
  intro i j
  rw [threeUnitPowerBasis_eval]
  apply Dvd.dvd.mul_left
  exact pow_dvd_pow_of_dvd (three_dvd_sq_sub_one_of_not_dvd (x i) (hunit i)) _

/-! ## Strengthened fixed divisors for positive dyadic units -/

/-- The first `v` positive odd integers are the dyadic-unit `2`-ordering centers. -/
noncomputable def twoUnitOrderingPolynomial (v : ℕ) : ℤ[X] :=
  ∏ t ∈ Finset.range v, (X - C (2 * (t : ℤ) + 1))

theorem twoUnitOrderingPolynomial_monic (v : ℕ) :
    (twoUnitOrderingPolynomial v).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro t _
  exact Polynomial.monic_X_sub_C _

theorem twoUnitOrderingPolynomial_natDegree (v : ℕ) :
    (twoUnitOrderingPolynomial v).natDegree = v := by
  rw [twoUnitOrderingPolynomial,
    Polynomial.natDegree_prod_of_monic (Finset.range v)
      (fun t ↦ (X - C (2 * (t : ℤ) + 1) : ℤ[X]))
      (fun t _ ↦ Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  rfl

theorem twoUnitOrderingPolynomial_eval (v z : ℕ) :
    (twoUnitOrderingPolynomial v).eval (2 * (z : ℤ) + 1) =
      (2 : ℤ) ^ v * ∏ t ∈ Finset.range v, ((z : ℤ) - t) := by
  rw [twoUnitOrderingPolynomial, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  calc
    (∏ t ∈ Finset.range v, (2 * (z : ℤ) + 1 - (2 * (t : ℤ) + 1))) =
        ∏ t ∈ Finset.range v, (2 : ℤ) * ((z : ℤ) - t) := by
      apply Finset.prod_congr rfl
      intro t _
      ring
    _ = (∏ _t ∈ Finset.range v, (2 : ℤ)) *
        ∏ t ∈ Finset.range v, ((z : ℤ) - t) := Finset.prod_mul_distrib
    _ = (2 : ℤ) ^ v * ∏ t ∈ Finset.range v, ((z : ℤ) - t) := by simp

theorem int_factorial_dvd_prod_range_sub (v z : ℕ) :
    (v.factorial : ℤ) ∣ ∏ t ∈ Finset.range v, ((z : ℤ) - t) := by
  by_cases hvz : v ≤ z
  · have heq :
        ((z.descFactorial v : ℕ) : ℤ) =
          ∏ t ∈ Finset.range v, ((z : ℤ) - t) := by
      rw [Nat.descFactorial_eq_prod_range]
      push_cast
      apply Finset.prod_congr rfl
      intro t ht
      have htz : t ≤ z := (Nat.le_of_lt (Finset.mem_range.mp ht)).trans hvz
      rw [Nat.cast_sub htz]
    rw [← heq]
    exact Int.natCast_dvd_natCast.mpr (Nat.factorial_dvd_descFactorial z v)
  · have hzmem : z ∈ Finset.range v := by simp; omega
    rw [Finset.prod_eq_zero hzmem]
    · exact dvd_zero _
    · simp

theorem twoUnitOrderingPolynomial_fixedDivisor (v z : ℕ) :
    (2 : ℤ) ^ (v + padicValNat 2 v.factorial) ∣
      (twoUnitOrderingPolynomial v).eval (2 * (z : ℤ) + 1) := by
  rw [twoUnitOrderingPolynomial_eval, pow_add]
  apply mul_dvd_mul dvd_rfl
  have hpNat : 2 ^ padicValNat 2 v.factorial ∣ v.factorial :=
    pow_padicValNat_dvd
  have hpInt : (2 : ℤ) ^ padicValNat 2 v.factorial ∣ (v.factorial : ℤ) := by
    exact_mod_cast hpNat
  exact hpInt.trans (int_factorial_dvd_prod_range_sub v z)

/-- **Strengthened dyadic-unit fixed divisor.**  The p-ordering basis improves
the simple `sum j` gain by the displayed factorial contribution
`sum v₂(j!)`. -/
def twoUnitOrderingWeight (j : ℕ) : ℕ :=
  j + padicValNat 2 j.factorial

theorem two_pow_sum_degree_add_factorialVal_dvd_det_vandermonde
    {n : ℕ} (z : Fin n → ℕ) :
    (2 : ℤ) ^ (∑ j : Fin n, twoUnitOrderingWeight (j : ℕ)) ∣
      (Matrix.vandermonde (fun i ↦ 2 * (z i : ℤ) + 1)).det := by
  apply pow_sum_dvd_det_vandermonde_of_monicBasis
    (fun i ↦ 2 * (z i : ℤ) + 1)
    (fun j ↦ twoUnitOrderingPolynomial (j : ℕ)) 2
    (fun j ↦ twoUnitOrderingWeight (j : ℕ))
  · intro j
    exact twoUnitOrderingPolynomial_natDegree _
  · intro j
    exact twoUnitOrderingPolynomial_monic _
  · intro i j
    simpa only [twoUnitOrderingWeight] using
      twoUnitOrderingPolynomial_fixedDivisor (j : ℕ) (z i)

/-! ## Strengthened fixed divisors for positive triadic units -/

/-- The triadic-unit p-ordering centers `1, 2, 4, 5, 7, 8, ...`. -/
def threeUnitOrderingCenter (t : ℕ) : ℤ :=
  3 * ((t / 2 : ℕ) : ℤ) + ((t % 2 : ℕ) : ℤ) + 1

noncomputable def threeUnitOrderingPolynomial (v : ℕ) : ℤ[X] :=
  ∏ t ∈ Finset.range v, (X - C (threeUnitOrderingCenter t))

theorem threeUnitOrderingPolynomial_monic (v : ℕ) :
    (threeUnitOrderingPolynomial v).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro t _
  exact Polynomial.monic_X_sub_C _

theorem threeUnitOrderingPolynomial_natDegree (v : ℕ) :
    (threeUnitOrderingPolynomial v).natDegree = v := by
  rw [threeUnitOrderingPolynomial,
    Polynomial.natDegree_prod_of_monic (Finset.range v)
      (fun t ↦ (X - C (threeUnitOrderingCenter t) : ℤ[X]))
      (fun t _ ↦ Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  rfl

theorem threeUnitOrderingPolynomial_eval (v : ℕ) (z : ℤ) :
    (threeUnitOrderingPolynomial v).eval z =
      ∏ t ∈ Finset.range v, (z - threeUnitOrderingCenter t) := by
  rw [threeUnitOrderingPolynomial, Polynomial.eval_prod]
  simp

def threeUnitOrderingWeight (j : ℕ) : ℕ :=
  j / 2 + padicValNat 3 (j / 2).factorial

theorem threeUnitOrderingPolynomial_fixedDivisor
    (v z : ℕ) (r : Fin 2) :
    (3 : ℤ) ^ threeUnitOrderingWeight v ∣
      (threeUnitOrderingPolynomial v).eval
        (3 * (z : ℤ) + (r : ℕ) + 1) := by
  let q := v / 2
  let g : ℕ → ℕ := fun s ↦ 2 * s + (r : ℕ)
  let S : Finset ℕ := (Finset.range q).image g
  let f : ℕ → ℤ := fun t ↦
    3 * (z : ℤ) + (r : ℕ) + 1 - threeUnitOrderingCenter t
  have hg : Function.Injective g := by
    intro a b hab
    dsimp only [g] at hab
    omega
  have hS : S ⊆ Finset.range v := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
    have hslt : s < q := Finset.mem_range.mp hs
    have hrlt : (r : ℕ) < 2 := r.isLt
    have hvmod : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
    simp only [Finset.mem_range, g]
    dsimp only [q] at hslt
    omega
  have hselected :
      (∏ t ∈ S, f t) =
        (3 : ℤ) ^ q * ∏ s ∈ Finset.range q, ((z : ℤ) - s) := by
    dsimp only [S]
    rw [Finset.prod_image (hg.injOn)]
    calc
      (∏ s ∈ Finset.range q, f (g s)) =
          ∏ s ∈ Finset.range q, (3 : ℤ) * ((z : ℤ) - s) := by
        apply Finset.prod_congr rfl
        intro s _
        have hrlt : (r : ℕ) < 2 := r.isLt
        have hdiv : (2 * s + (r : ℕ)) / 2 = s := by omega
        have hmod : (2 * s + (r : ℕ)) % 2 = (r : ℕ) := by omega
        dsimp only [f, g, threeUnitOrderingCenter]
        rw [hdiv, hmod]
        ring
      _ = (∏ _s ∈ Finset.range q, (3 : ℤ)) *
          ∏ s ∈ Finset.range q, ((z : ℤ) - s) := Finset.prod_mul_distrib
      _ = (3 : ℤ) ^ q * ∏ s ∈ Finset.range q, ((z : ℤ) - s) := by simp
  have hselected_dvd :
      (3 : ℤ) ^ threeUnitOrderingWeight v ∣ ∏ t ∈ S, f t := by
    rw [hselected, threeUnitOrderingWeight, pow_add]
    apply mul_dvd_mul dvd_rfl
    have hpNat : 3 ^ padicValNat 3 q.factorial ∣ q.factorial :=
      pow_padicValNat_dvd
    have hpInt : (3 : ℤ) ^ padicValNat 3 q.factorial ∣ (q.factorial : ℤ) := by
      exact_mod_cast hpNat
    exact hpInt.trans (int_factorial_dvd_prod_range_sub q z)
  rw [threeUnitOrderingPolynomial_eval]
  exact hselected_dvd.trans
    (Finset.prod_dvd_prod_of_subset S (Finset.range v) f hS)

/-- **Strengthened triadic-unit fixed divisor.**  Alternating the two nonzero
residue classes gives the displayed weight
`floor(j/2)+v₃(floor(j/2)!)` in every degree. -/
theorem three_pow_sum_halfDegree_add_factorialVal_dvd_det_vandermonde
    {n : ℕ} (z : Fin n → ℕ) (r : Fin n → Fin 2) :
    (3 : ℤ) ^ (∑ j : Fin n, threeUnitOrderingWeight (j : ℕ)) ∣
      (Matrix.vandermonde
        (fun i ↦ 3 * (z i : ℤ) + ((r i : ℕ) : ℤ) + 1)).det := by
  apply pow_sum_dvd_det_vandermonde_of_monicBasis
    (fun i ↦ 3 * (z i : ℤ) + ((r i : ℕ) : ℤ) + 1)
    (fun j ↦ threeUnitOrderingPolynomial (j : ℕ)) 3
    (fun j ↦ threeUnitOrderingWeight (j : ℕ))
  · intro j
    exact threeUnitOrderingPolynomial_natDegree _
  · intro j
    exact threeUnitOrderingPolynomial_monic _
  · intro i j
    exact threeUnitOrderingPolynomial_fixedDivisor (j : ℕ) (z i) (r i)

end LeanProofs.TwoBaseIntegerExponent
