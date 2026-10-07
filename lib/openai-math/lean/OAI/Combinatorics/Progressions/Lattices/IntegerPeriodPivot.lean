import OAI.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerPeriod_exists_pivot {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J]
    (A : Matrix O J ℤ) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice O a ≤ A.mulVecLin.range) :
    ∃ s : O ↪ J, (A.submatrix id s).det ≠ 0 := by
  classical
  have hcol (i : O) : ∃ v : J → ℤ, A *ᵥ v = a • Pi.single i 1 :=
    hperiod ((integerScalarLattice_mem a _).mpr ⟨Pi.single i 1, rfl⟩)
  choose v hv using hcol
  let B : Matrix J O ℤ := fun j i => v i j
  have hAB : A * B = a • (1 : Matrix O O ℤ) := by
    ext i k
    change (A *ᵥ v k) i = (a • (1 : Matrix O O ℤ)) i k
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply,
      Pi.single_apply, eq_comm] using congrFun (hv k) i
  have hdet : (A * B).det ≠ 0 := by
    rw [hAB, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ ha
  rw [rectangular_det_expansion] at hdet
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hminor : (A.submatrix id s).det ≠ 0 := left_ne_zero_of_mul hs
  refine ⟨⟨s, ?_⟩, hminor⟩
  intro i j hij
  by_contra hne
  apply hminor
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, hij])

theorem boundedCoefficientJetMatrix_exists_pivot {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (A : Matrix α K ℤ) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ A.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    ∃ s : O ↪ VectorPolynomial.BoundedCoefficientExponent K h,
      ((boundedCoefficientJetMatrix root A h rows).submatrix id s).det ≠ 0 :=
  integerPeriod_exists_pivot (boundedCoefficientJetMatrix root A h rows) (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root A a hperiod h rows hinj hdegree)

end Erdos3

end

end OAI
