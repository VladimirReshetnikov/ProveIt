import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import OAI.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization

namespace OAI


namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

noncomputable def translationDirectionalDerivative (b : B → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ →ₗ[ℝ] MvPolynomial (U ⊕ B) ℝ :=
  ∑ i, (LinearMap.mulLeft ℝ (rename Sum.inl (b i))).comp (pderiv (Sum.inr i)).toLinearMap

theorem translationDirectionalDerivative_apply (b : B → MvPolynomial U ℝ)
    (P : MvPolynomial (U ⊕ B) ℝ) :
    translationDirectionalDerivative b P =
      ∑ i, rename Sum.inl (b i) * pderiv (Sum.inr i) P := by
  simp [translationDirectionalDerivative]

noncomputable def translationDirectionalSeries (d : ℕ) (b : B → MvPolynomial U ℝ)
    (P : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  ∑ i ∈ Finset.range d, ((-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)) •
    ((translationDirectionalDerivative b) ^ i) P

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

omit [Fintype B] in
theorem degreeOf_rename_inl_inr (P : MvPolynomial U ℝ) (i : B) :
    (rename (Sum.inl : U → U ⊕ B) P).degreeOf (Sum.inr i) = 0 := by
  classical
  by_contra h
  obtain ⟨j, _, hj⟩ := mem_vars_rename (Sum.inl : U → U ⊕ B) P
    (mem_vars_iff_degreeOf_ne_zero.mpr h)
  cases hj

theorem translationDirectionalDerivative_degreeOf_le
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d) (j : B) :
    (translationDirectionalDerivative b P).degreeOf (Sum.inr j) ≤ d := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro i _
  apply (degreeOf_mul_le _ _ _).trans
  rw [degreeOf_rename_inl_inr, zero_add]
  exact mvPolynomial_pderiv_degreeOf_le P (Sum.inr i) (Sum.inr j) (hP j)

theorem translationDirectionalDerivative_pow_degreeOf_le
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d) (k : ℕ) (j : B) :
    (((translationDirectionalDerivative b) ^ k) P).degreeOf (Sum.inr j) ≤ d := by
  induction k generalizing j with
  | zero => simpa using hP j
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_degreeOf_le b _ d ih j

theorem realPolynomialMass_translationDirectionalDerivative
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M) :
    realPolynomialMass (translationDirectionalDerivative b P) ≤
      ((Fintype.card B : ℝ) * d * M) * realPolynomialMass P := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : B, M * ((d : ℝ) * realPolynomialMass P) := by
      apply Finset.sum_le_sum
      intro i _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul ((realPolynomialMass_rename_le _ _).trans (hb i))
          (realPolynomialMass_pderiv_degreeOf P (Sum.inr i) (hP i))
          (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

theorem realPolynomialMass_translationDirectionalDerivative_pow
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M) (k : ℕ) :
    realPolynomialMass (((translationDirectionalDerivative b) ^ k) P) ≤
      ((Fintype.card B : ℝ) * d * M) ^ k * realPolynomialMass P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    apply (realPolynomialMass_translationDirectionalDerivative b _ d
      (translationDirectionalDerivative_pow_degreeOf_le b P d hP k) hM hb).trans
    calc
      _ ≤ ((Fintype.card B : ℝ) * d * M) *
          (((Fintype.card B : ℝ) * d * M) ^ k * realPolynomialMass P) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ']; ring

theorem translationDirectionalSeries_coefficient_abs_le_one (i : ℕ) :
    |(-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)| ≤ 1 := by
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Nat.cast_nonneg _)]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (i + 1))

theorem realPolynomialMass_translationDirectionalSeries
    (d : ℕ) (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M)
    (hmass : realPolynomialMass P ≤ M) :
    realPolynomialMass (translationDirectionalSeries d b P) ≤
      ((d : ℝ) + 1) * M * (1 + (Fintype.card B : ℝ) * d * M) ^ d := by
  classical
  let A : ℝ := (Fintype.card B : ℝ) * d * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hterm (i : ℕ) (hi : i ∈ Finset.range d) :
      realPolynomialMass (((-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)) •
        ((translationDirectionalDerivative b) ^ i) P) ≤ M * (1 + A) ^ d := by
    rw [realPolynomialMass_smul]
    calc
      _ ≤ 1 * (A ^ i * realPolynomialMass P) :=
        mul_le_mul (translationDirectionalSeries_coefficient_abs_le_one i)
          (realPolynomialMass_translationDirectionalDerivative_pow b P d hP hM hb i)
          (realPolynomialMass_nonneg _) (by norm_num)
      _ ≤ A ^ i * M := by simpa using mul_le_mul_of_nonneg_left hmass (pow_nonneg hA i)
      _ ≤ (1 + A) ^ d * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact (pow_le_pow_left₀ hA (by linarith) i).trans
          (pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hi).le)
      _ = _ := mul_comm _ _
  unfold translationDirectionalSeries
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range d, M * (1 + A) ^ d := Finset.sum_le_sum hterm
    _ = (d : ℝ) * (M * (1 + A) ^ d) := by simp
    _ ≤ ((d : ℝ) + 1) * (M * (1 + A) ^ d) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by dsimp [A]; ring

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem isWeightedHomogeneous_aeval_monomial (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i)) (a : σ →₀ ℕ) (r : R) :
    (aeval f (monomial a r)).IsWeightedHomogeneous w (Finsupp.weight v a) := by
  classical
  rw [aeval_monomial]
  have hprod := IsWeightedHomogeneous.prod a.support (fun i => f i ^ a i)
    (fun i => a i * v i) (fun i _ => by simpa using (hf i).pow (a i))
  have hweight : (∑ i ∈ a.support, a i * v i) = Finsupp.weight v a := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [MvPolynomial.algebraMap_eq, Finsupp.prod] using hprod.C_mul r

theorem isWeightedHomogeneous_algHom (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, (F (X i)).IsWeightedHomogeneous w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous v n) :
    (F p).IsWeightedHomogeneous w n := by
  classical
  rw [MvPolynomial.aeval_unique F]
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply IsWeightedHomogeneous.sum
  intro a ha
  have hweight : Finsupp.weight v a = n := hp (mem_support_iff.mp ha)
  rw [← hweight]
  exact isWeightedHomogeneous_aeval_monomial v w (fun i => F (X i)) hF a _

theorem weightedHomogeneousComponent_eq_of_sub_lower (w : σ → ℕ)
    {p q : MvPolynomial σ R} {n : ℕ}
    (hpq : p - q ∈ weightedSupportLT w n) (hq : q.IsWeightedHomogeneous w n) :
    weightedHomogeneousComponent w n p = q := by
  have hzero : weightedHomogeneousComponent w n (p - q) = 0 := by
    apply MvPolynomial.ext
    intro a
    rw [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero]
    split_ifs with ha
    · by_contra hc
      have hlt := hpq (mem_support_iff.mpr hc)
      change Finsupp.weight w a < n at hlt
      omega
    · rfl
  rw [map_sub, hq.weightedHomogeneousComponent_same, sub_eq_zero] at hzero
  exact hzero

theorem aeval_isWeightedHomogeneous (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous v n) :
    (aeval f p).IsWeightedHomogeneous w n := by
  apply isWeightedHomogeneous_algHom v w (aeval f) _ hp
  intro i
  simpa only [aeval_X] using hf i

theorem aeval_weightedHomogeneousComponent (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i))
    (n : ℕ) (p : MvPolynomial σ R) :
    aeval f (weightedHomogeneousComponent v n p) =
      weightedHomogeneousComponent w n (aeval f p) := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro α _
  have hm := isWeightedHomogeneous_monomial v α (p.coeff α) rfl
  have hfα := isWeightedHomogeneous_aeval_monomial v w f hf α (p.coeff α)
  by_cases h : n = Finsupp.weight v α
  · rw [h, hm.weightedHomogeneousComponent_same, hfα.weightedHomogeneousComponent_same]
  · rw [hm.weightedHomogeneousComponent_ne n h, map_zero,
      hfα.weightedHomogeneousComponent_ne n h]

end Erdos3


namespace Erdos3

open MvPolynomial
open scoped BigOperators

theorem isWeightedHomogeneous_mul_pderiv {σ R : Type*} [CommRing R]
    (w : σ → ℕ) (i : σ) {Q P : MvPolynomial σ R} {d : ℕ}
    (hQ : Q.IsWeightedHomogeneous w (w i)) (hP : P.IsWeightedHomogeneous w d) :
    (Q * pderiv i P).IsWeightedHomogeneous w d := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum, Finset.mul_sum]
  apply (weightedHomogeneousSubmodule R w d).sum_mem
  intro a ha
  change (Q * pderiv i (monomial a (P.coeff a))).IsWeightedHomogeneous w d
  rw [pderiv_monomial]
  by_cases hi : a i = 0
  · simp only [hi, Nat.cast_zero, mul_zero, monomial_zero]
    exact (weightedHomogeneousSubmodule R w d).zero_mem
  · have hweight := Finsupp.weight_sub_single_add (w := w) hi
    rw [hP (MvPolynomial.mem_support_iff.mp ha)] at hweight
    have hm := hQ.mul (isWeightedHomogeneous_monomial w
      (a - Finsupp.single i 1) (P.coeff a * (a i : R)) rfl)
    simpa only [Nat.add_comm (w i), hweight] using hm

variable {U B : Type*} [Fintype B]

theorem translationDirectionalDerivative_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) :
    (translationDirectionalDerivative b P).IsWeightedHomogeneous (Sum.elim v w) d := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro i _
  apply isWeightedHomogeneous_mul_pderiv (Sum.elim v w) (Sum.inr i) _ hP
  rw [rename_eq_aeval]
  exact aeval_isWeightedHomogeneous v (Sum.elim v w) (X ∘ Sum.inl)
    (fun j => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inl j)) (hb i)

theorem translationDirectionalDerivative_pow_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) (n : ℕ) :
    (((translationDirectionalDerivative b) ^ n) P).IsWeightedHomogeneous
      (Sum.elim v w) d := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_isWeightedHomogeneous v w b hb ih

theorem translationDirectionalSeries_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (N : ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) :
    (translationDirectionalSeries N b P).IsWeightedHomogeneous (Sum.elim v w) d := by
  classical
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro i _
  exact (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).smul_mem _
    (translationDirectionalDerivative_pow_isWeightedHomogeneous v w b hb hP i)

end Erdos3


namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem scaleMvPolynomialAxes_weightedHomogeneousComponent
    (w : σ → ℕ) (T : σ → ℝ) (d : ℕ) (P : MvPolynomial σ ℝ) :
    weightedHomogeneousComponent w d (scaleMvPolynomialAxes T P) =
      scaleMvPolynomialAxes T (weightedHomogeneousComponent w d P) := by
  classical
  ext α
  simp only [coeff_weightedHomogeneousComponent, scaleMvPolynomialAxes_coeff]
  split_ifs <;> simp

end Erdos3

end OAI
