import OAI.Combinatorics.Progressions.Geometry.TranslationLogCoordinateInputBounds

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ U B : Type*}

theorem realPolynomialCoefficientGrid_zero (q : ℕ) :
    realPolynomialCoefficientGrid q (0 : MvPolynomial σ ℝ) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  simp

theorem realPolynomialCoefficientGrid_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) {q : ℕ}
    (hP : ∀ i ∈ s, realPolynomialCoefficientGrid q (P i)) :
    realPolynomialCoefficientGrid q (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realPolynomialCoefficientGrid_zero q
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact realPolynomialCoefficientGrid_add (hP i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem realPolynomialCoefficientGrid_mul {q r : ℕ} {P Q : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) (hQ : realPolynomialCoefficientGrid r Q) :
    realPolynomialCoefficientGrid (q * r) (P * Q) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  have h := (integralRealPolynomialSubring σ).mul_mem
    ((realPolynomialCoefficientGrid_iff _ _).mp hP)
    ((realPolynomialCoefficientGrid_iff _ _).mp hQ)
  simpa only [Nat.cast_mul, map_mul, mul_mul_mul_comm] using h

theorem realPolynomialCoefficientGrid_pderiv (i : σ) {q : ℕ}
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (pderiv i P) := by
  obtain ⟨I, hI⟩ := (realPolynomialCoefficientGrid_iff _ _).mp hP
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  refine ⟨pderiv i I, ?_⟩
  rw [← pderiv_map, hI, pderiv_C_mul]

theorem realPolynomialCoefficientGrid_rat_smul (z : ℤ) {t r : ℕ} (ht : 0 < t)
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid r P) :
    realPolynomialCoefficientGrid (t * r) (((z : ℝ) / (t : ℝ)) • P) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  have h := (integralRealPolynomialSubring σ).mul_mem
    (C_int_mem_integralRealPolynomialSubring z)
    ((realPolynomialCoefficientGrid_iff _ _).mp hP)
  have heq : C ((t * r : ℕ) : ℝ) * (((z : ℝ) / (t : ℝ)) • P) =
      C (z : ℝ) * (C (r : ℝ) * P) := by
    rw [← C_mul', ← mul_assoc, ← map_mul]
    have hs : ((t * r : ℕ) : ℝ) * ((z : ℝ) / (t : ℝ)) = (z : ℝ) * (r : ℝ) := by
      push_cast
      field_simp
    rw [hs, map_mul, mul_assoc]
  rw [heq]
  exact h

variable [Fintype B]

theorem translationDirectionalDerivative_coefficientGrid
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q r : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid r P) :
    realPolynomialCoefficientGrid (q * r) (translationDirectionalDerivative b P) := by
  rw [translationDirectionalDerivative_apply]
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun i _ =>
    realPolynomialCoefficientGrid_mul (realPolynomialCoefficientGrid_rename Sum.inl (hb i))
      (realPolynomialCoefficientGrid_pderiv (Sum.inr i) hP)

theorem translationDirectionalDerivative_pow_coefficientGrid
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid q P) (i : ℕ) :
    realPolynomialCoefficientGrid (q ^ (i + 1)) (((translationDirectionalDerivative b) ^ i) P) := by
  induction i with
  | zero => simpa using hP
  | succ i ih =>
      simpa only [pow_succ', Module.End.mul_apply] using
        translationDirectionalDerivative_coefficientGrid b _ hb ih

theorem translationDirectionalSeries_coefficientGrid (d : ℕ)
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (translationDirectionalSeries d b P) := by
  unfold translationDirectionalSeries
  apply realPolynomialCoefficientGrid_sum
  intro i hi
  have hid : i + 1 ≤ d := Finset.mem_range.mp hi
  have hterm := realPolynomialCoefficientGrid_rat_smul ((-1 : ℤ) ^ i)
    (Nat.factorial_pos (i + 1))
    (translationDirectionalDerivative_pow_coefficientGrid b P hb hP i)
  have hdiv : (i + 1).factorial * q ^ (i + 1) ∣ d.factorial * q ^ (d + 1) :=
    Nat.mul_dvd_mul (Nat.factorial_dvd_factorial hid) (pow_dvd_pow q (by omega))
  apply realPolynomialCoefficientGrid_mono hdiv
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hterm

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped BigOperators

variable {U B κ : Type*} [Fintype B] [Fintype κ]

private theorem constant_coefficientGrid {l : ℕ} {a : ℝ}
    (ha : ∃ z : ℤ, (z : ℝ) = (l : ℝ) * a) :
    realPolynomialCoefficientGrid l (C a : MvPolynomial U ℝ) := by
  obtain ⟨z, hz⟩ := ha
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  rw [← map_mul, ← hz]
  exact C_int_mem_integralRealPolynomialSubring z

theorem translationLogBasePolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (i : B) :
    realPolynomialCoefficientGrid (q * l) (translationLogBasePolynomial w d x f i) := by
  unfold translationLogBasePolynomial
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun k _ =>
    realPolynomialCoefficientGrid_mul (hf k) (constant_coefficientGrid (hbase k i))

theorem pack_translationLogPhasePolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (q * l)
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) := by
  rw [pack_translationLogPhasePolynomial]
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun k _ =>
    realPolynomialCoefficientGrid_mul (realPolynomialCoefficientGrid_rename Sum.inl (hf k))
      (realPolynomialCoefficientGrid_rename Sum.inr (hphase k))

theorem translationLogDirectionalSeries_coefficientGrid (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (d.factorial * (q * l) ^ (d + 1))
      (translationDirectionalSeries d (translationLogBasePolynomial w d x f)
        (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) :=
  translationDirectionalSeries_coefficientGrid d _ _
    (translationLogBasePolynomial_coefficientGrid w d x f hf hbase)
    (pack_translationLogPhasePolynomial_coefficientGrid w d x f hf hphase)

end Erdos3.PolynomialTranslationLie

end

end OAI
