/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) : MvPolynomial τ ℚ := by
  classical
  exact ∑ j, A (Pi.single j 1) i • X j

noncomputable def polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ :=
  aeval (linearCoordinatePolynomial A)

omit [Fintype σ] in
theorem linearMap_apply_sum_coordinates [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (i : σ) :
    ∑ j, A (Pi.single j 1) i * x j = A x i := by
  classical
  have hx : (∑ j, x j • Pi.single j (1 : ℚ)) = x := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

omit [Fintype σ] in
@[simp] theorem polynomialLinearRestriction_X
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    polynomialLinearRestriction A (X i) = linearCoordinatePolynomial A i := by
  simp [polynomialLinearRestriction]

omit [Fintype σ] in
@[simp] theorem polynomialLinearRestriction_C
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (r : ℚ) :
    polynomialLinearRestriction A (C r) = C r := by
  simp [polynomialLinearRestriction]

omit [Fintype σ] in
@[simp] theorem eval_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (i : σ) :
    eval x (linearCoordinatePolynomial A i) = A x i := by
  classical
  simp only [linearCoordinatePolynomial, map_sum, ← C_mul', map_mul, eval_C, eval_X]
  exact linearMap_apply_sum_coordinates A x i

omit [Fintype σ] in
@[simp] theorem scalarDirectionalDerivative_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    scalarDirectionalDerivative z (linearCoordinatePolynomial A i) = C (A z i) := by
  classical
  rw [linearCoordinatePolynomial, map_sum]
  simp only [Derivation.map_smul, scalarDirectionalDerivative_X]
  simp only [← C_mul', ← map_mul]
  rw [← map_sum, linearMap_apply_sum_coordinates]

omit [Fintype σ] in
theorem eval_polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (P : MvPolynomial σ ℚ) :
    eval x (polynomialLinearRestriction A P) = eval (A x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem scalarDirectionalDerivative_linearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative z (polynomialLinearRestriction A P) =
      polynomialLinearRestriction A (scalarDirectionalDerivative (A z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

omit [Fintype σ] in
@[simp] theorem coeff_zero_polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) :
    (polynomialLinearRestriction A P).coeff 0 = P.coeff 0 := by
  have h := eval_polynomialLinearRestriction A 0 P
  simpa only [map_zero, eval_zero, constantCoeff_eq] using h

omit [Fintype σ] in
theorem polynomialTranslate_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    polynomialTranslate z (linearCoordinatePolynomial A i) =
      linearCoordinatePolynomial A i + C (A z i) := by
  classical
  rw [linearCoordinatePolynomial, map_sum]
  simp only [map_smul, polynomialTranslate_X, smul_add, Finset.sum_add_distrib]
  congr 1
  simp only [← C_mul', ← map_mul]
  rw [← map_sum, linearMap_apply_sum_coordinates]

omit [Fintype σ] in
theorem polynomialLinearRestriction_translate
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialLinearRestriction A (polynomialTranslate (A z) P) =
      polynomialTranslate z (polynomialLinearRestriction A P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, polynomialTranslate_linearCoordinatePolynomial]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem polynomialTranslationPath_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    polynomialTranslationPath z (linearCoordinatePolynomial A i) =
      Polynomial.C (linearCoordinatePolynomial A i) -
        Polynomial.C (C (A z i)) * Polynomial.X := by
  classical
  have hsum : (∑ j, A (Pi.single j 1) i • C (z j)) = (C (A z i) : MvPolynomial τ ℚ) := by
    simp only [← C_mul', ← map_mul, ← map_sum, linearMap_apply_sum_coordinates]
  rw [linearCoordinatePolynomial, map_sum]
  simp only [map_smul, polynomialTranslationPath_X, smul_sub,
    Finset.sum_sub_distrib, ← smul_mul_assoc, Polynomial.smul_C]
  rw [← map_sum, ← Finset.sum_mul, ← map_sum, hsum]

theorem polynomialLinearRestriction_translationPath
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    (polynomialTranslationPath (A z) P).map (polynomialLinearRestriction A).toRingHom =
      polynomialTranslationPath z (polynomialLinearRestriction A P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.map_mul, hp]
    simp [polynomialTranslationPath_linearCoordinatePolynomial]

theorem polynomialLinearRestriction_exponentialPath
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    (polynomialExponentialPath (A z) P).map (polynomialLinearRestriction A).toRingHom =
      polynomialExponentialPath z (polynomialLinearRestriction A P) := by
  symm
  apply polynomialExponentialPath_unique
  · rw [Polynomial.derivative_map, polynomialExponentialPath_derivative,
      polynomialLinearRestriction_translationPath]
  · simp

theorem polynomialLinearRestriction_exponentialCoordinate
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    polynomialLinearRestriction A (polynomialExponentialCoordinate (A z) P) =
      polynomialExponentialCoordinate z (polynomialLinearRestriction A P) := by
  unfold polynomialExponentialCoordinate
  rw [← polynomialLinearRestriction_exponentialPath]
  simp

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem linearCoordinatePolynomial_eq_sum [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    linearCoordinatePolynomial A i = ∑ j, A (Pi.single j 1) i • (X j : MvPolynomial τ ℚ) := by
  unfold linearCoordinatePolynomial
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun c : ℚ => c • (X j : MvPolynomial τ ℚ))
  apply congrArg (fun x : τ → ℚ => A x i)
  funext k
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

theorem linearCoordinatePolynomial_isWeightedHomogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) (i : σ) :
    (linearCoordinatePolynomial A i).IsWeightedHomogeneous v (w i) := by
  rw [linearCoordinatePolynomial_eq_sum]
  apply (weightedHomogeneousSubmodule ℚ v (w i)).sum_mem
  intro j _
  by_cases hj : v j = w i
  · exact hj ▸ (weightedHomogeneousSubmodule ℚ v (v j)).smul_mem
      (A (Pi.single j 1) i) (isWeightedHomogeneous_X (R := ℚ) v j)
  · rw [hA j i hj, zero_smul]
    exact isWeightedHomogeneous_zero ℚ v (w i)

theorem polynomialLinearRestriction_monomial_homogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (a : σ →₀ ℕ) (c : ℚ) :
    (polynomialLinearRestriction A (monomial a c)).IsWeightedHomogeneous v (Finsupp.weight w a) := by
  rw [monomial_eq]
  simp only [map_mul, polynomialLinearRestriction_C, Finsupp.prod, map_prod,
    map_pow, polynomialLinearRestriction_X]
  have hprod := IsWeightedHomogeneous.prod a.support
    (fun i => linearCoordinatePolynomial A i ^ a i) (fun i => a i * w i)
    (fun i _ => by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (linearCoordinatePolynomial_isWeightedHomogeneous A v w hA i).pow (a i))
  simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id] using hprod.C_mul c

theorem polynomialLinearRestriction_isWeightedHomogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P.IsWeightedHomogeneous w n) :
    (polynomialLinearRestriction A P).IsWeightedHomogeneous v n := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedHomogeneousSubmodule ℚ v n).sum_mem
  intro a ha
  have h := polynomialLinearRestriction_monomial_homogeneous A v w hA a (P.coeff a)
  change (polynomialLinearRestriction A (monomial a (P.coeff a))).IsWeightedHomogeneous v n
  simpa only [hP (MvPolynomial.mem_support_iff.mp ha)] using h

theorem polynomialLinearRestriction_weightedHomogeneousComponent [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (n : ℕ) (P : MvPolynomial σ ℚ) :
    polynomialLinearRestriction A (weightedHomogeneousComponent w n P) =
      weightedHomogeneousComponent v n (polynomialLinearRestriction A P) := by
  conv_lhs => rw [← P.support_sum_monomial_coeff]
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial w a (P.coeff a) rfl),
    weightedHomogeneousComponent_of_mem (polynomialLinearRestriction_monomial_homogeneous
      A v w hA a (P.coeff a))]
  split_ifs <;> simp

theorem polynomialLinearRestriction_mem_weightedSupportDrop [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    {P : MvPolynomial σ ℚ} {n r : ℕ} (hP : P ∈ weightedSupportDrop w n r) :
    polynomialLinearRestriction A P ∈ weightedSupportDrop v n r := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportDrop v n r).sum_mem
  intro a ha b hb
  have he := polynomialLinearRestriction_monomial_homogeneous A v w hA a (P.coeff a)
    (MvPolynomial.mem_support_iff.mp hb)
  change Finsupp.weight v b + r ≤ n
  rw [he]
  exact hP ha

theorem polynomialLinearRestriction_mem_weightedSupportLT [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLT w n) :
    polynomialLinearRestriction A P ∈ weightedSupportLT v n := by
  rw [← weightedSupportDrop_one] at hP ⊢
  exact polynomialLinearRestriction_mem_weightedSupportDrop A v w hA hP

namespace PolynomialTranslationLie

variable [Fintype σ]

theorem weightedBasis_projection_polynomial_eq_component (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (hj : j ≤ d) (x : weightedSubalgebra w d) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.polynomial =
      weightedHomogeneousComponent w (d - j) x.val.polynomial := by
  apply MvPolynomial.ext
  intro a
  by_cases ha : Finsupp.weight w a < d
  · rw [weightedBasis_projection_coeff w d j hw x ⟨a, ha⟩,
      coeff_weightedHomogeneousComponent]
    have he : d - Finsupp.weight w a = j ↔ Finsupp.weight w a = d - j := by omega
    simp only [he]
  · have hzero : x.val.polynomial.coeff a = 0 := by
      by_contra hne
      have hb := x.property.2 (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w a + 1 ≤ d at hb
      omega
    rw [coeff_weightedHomogeneousComponent, hzero, ite_self]
    by_contra hne
    have hb := (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).property.2
      (MvPolynomial.mem_support_iff.mpr hne)
    change Finsupp.weight w a + 1 ≤ d at hb
    omega

theorem weightedBasis_projection_eq_zero_of_lt (w : σ → ℕ) (d j : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (hj : d < j)
    (x : weightedSubalgebra w d) :
    basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x = 0 := by
  apply (weightedBasis w d hw).repr.injective
  ext i
  rw [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  exact ite_eq_right (Nat.ne_of_lt ((weightedBasisGrade_le w d hwd i).trans_lt hj))

end PolynomialTranslationLie
end Erdos3

end

end OAI
