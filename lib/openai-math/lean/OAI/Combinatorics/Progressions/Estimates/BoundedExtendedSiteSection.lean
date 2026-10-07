import OAI.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def columnInclusionMatrix {I K : Type*} [DecidableEq I] (e : K → I) : Matrix I K ℝ :=
  fun i k => if e k = i then 1 else 0

theorem matrix_mul_columnInclusion {I K S : Type*} [Fintype I] [DecidableEq I]
    (E : Matrix S I ℝ) (e : K → I) : E * columnInclusionMatrix e = E.submatrix id e := by
  ext s k
  simp [Matrix.mul_apply, columnInclusionMatrix]

theorem columnInclusion_transpose_mul {I K J : Type*} [Fintype I] [DecidableEq I]
    (e : K → I) (F : Matrix I J ℝ) : (columnInclusionMatrix e)ᵀ * F = F.submatrix e id := by
  ext k j
  simp [Matrix.mul_apply, columnInclusionMatrix]

theorem exists_common_site_denominator_from_columns :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K S : Type*}
    [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S]
    (E₀ : Matrix S K ℚ) {H : ℕ} (_hH : 1 ≤ H)
    (_hE₀ : ∀ s k, RationalHeightLE (E₀ s k) H)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K : ℝ) ≤ P)
    (_hS : (Fintype.card S : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E : Matrix S I ℚ) (e : K → I) (_hcolumns : E.submatrix id e = E₀)
    (R : Matrix K I ℝ)
    (_himage : Matrix.of (fun s k => (E₀ s k : ℝ)) * R = Matrix.of (fun s i => (E s i : ℝ)))
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ k a, |(frequency (e k) a : ℝ)| ≤ C)
    (M : (S → U) →ₗ[ℝ] ℝ)
    (_hfactor : ∀ x, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      M (matrixModuleAction (fun s i => (E s i : ℝ)) x)),
    ∃ b : Matrix S J ℤ, (∀ s a, |(b s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ x : I → U, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
        subspaceArrayFunctional U (fun s a => (b s a : ℝ))
          (matrixModuleAction (fun s i => (E s i : ℝ)) ((q : ℝ)⁻¹ • x)) := by
  obtain ⟨A, hA, hcover⟩ := exists_common_site_denominator
  refine ⟨A, hA, ?_⟩
  intro K S _ _ _ _ E₀ H hH hE₀ P hP hK hS hHP
  obtain ⟨q, hq, hqP, hrows⟩ := hcover E₀ hH hE₀ hP hK hS hHP
  refine ⟨q, hq, hqP, ?_⟩
  intro I J _ _ _ E e hcolumns R himage U frequency C hC hCP hfrequency M hfactor
  have hcols : (Matrix.of (fun s i => (E s i : ℝ))).submatrix id e =
      Matrix.of (fun s k => (E₀ s k : ℝ)) := by
    ext s k
    exact congrArg (fun r : ℚ => (r : ℝ)) (congrFun (congrFun hcolumns s) k)
  have hf₀ (x : K → U) : subspaceArrayFunctional U (fun k a => (frequency (e k) a : ℝ)) x =
      M (matrixModuleAction (fun s k => (E₀ s k : ℝ)) x) := by
    have hf := hfactor (matrixModuleAction (columnInclusionMatrix e) x)
    change subspaceArrayFunctional U (Matrix.of (fun i a => (frequency i a : ℝ)))
      (matrixModuleAction (columnInclusionMatrix e) x) =
        M (matrixModuleAction (Matrix.of (fun s i => (E s i : ℝ)))
          (matrixModuleAction (columnInclusionMatrix e) x)) at hf
    rw [subspaceArrayFunctional_matrix U (columnInclusionMatrix e)
      (Matrix.of (fun i a => (frequency i a : ℝ))) x, columnInclusion_transpose_mul,
      matrixModuleAction_mul (Matrix.of (fun s i => (E s i : ℝ))) (columnInclusionMatrix e) x,
      matrix_mul_columnInclusion, hcols] at hf
    exact hf
  obtain ⟨b, hb, he⟩ := hrows U (fun k a => frequency (e k) a) hC hCP hfrequency M hf₀
  refine ⟨b, hb, ?_⟩
  intro x
  have hy : matrixModuleAction (fun s k => (E₀ s k : ℝ)) (matrixModuleAction R x) =
      matrixModuleAction (fun s i => (E s i : ℝ)) x := by
    change matrixModuleAction (Matrix.of (fun s k => (E₀ s k : ℝ))) (matrixModuleAction R x) =
      matrixModuleAction (Matrix.of (fun s i => (E s i : ℝ))) x
    rw [matrixModuleAction_mul (Matrix.of (fun s k => (E₀ s k : ℝ))) R x, himage]
  have h := he (matrixModuleAction R x)
  rw [hf₀, hy, map_smul, hy] at h
  rw [hfactor, map_smul]
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def extendIntegerSiteSection {K I S : Type*} [Fintype K] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) : Matrix I S ℤ :=
  fun i s => ∑ k, if e k = i then T k s else 0

theorem extendIntegerSiteSection_cast {K I S : Type*} [Fintype K] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) :
    Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ)) =
      columnInclusionMatrix e * Matrix.of (fun k s => (T k s : ℝ)) := by
  ext i s
  simp [extendIntegerSiteSection, columnInclusionMatrix, Matrix.mul_apply]

theorem integerSiteResidual_extend_columns {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S]
    (E₀ : Matrix S K ℤ) (E : Matrix S I ℤ) (e : K → I)
    (hcolumns : E.submatrix id e = E₀) (R : Matrix K I ℝ)
    (himage : Matrix.of (fun s k => (E₀ s k : ℝ)) * R = Matrix.of (fun s i => (E s i : ℝ)))
    (T : Matrix K S ℤ) (q : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (hT : ∀ (x : K → W),
      matrixModuleAction (fun s k => (E₀ s k : ℝ))
        (matrixModuleAction (fun k s => (T k s : ℝ))
          (matrixModuleAction (fun s k => (E₀ s k : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s k => (E₀ s k : ℝ)) x)
    (x : I → W) :
    matrixModuleAction (fun s i => (E s i : ℝ))
      (matrixModuleAction (fun i s => (extendIntegerSiteSection e T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
      (q : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  let E₀' := Matrix.of (fun s k => (E₀ s k : ℝ))
  let E' := Matrix.of (fun s i => (E s i : ℝ))
  let T' := Matrix.of (fun k s => (T k s : ℝ))
  let U' := Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ))
  have hc : E'.submatrix id e = E₀' := by
    ext s k
    exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun (congrFun hcolumns s) k)
  have hET : E' * U' = E₀' * T' := by
    change E' * Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ)) = E₀' * T'
    rw [extendIntegerSiteSection_cast, ← Matrix.mul_assoc, matrix_mul_columnInclusion, hc]
  have hact (v : S → W) : matrixModuleAction E' (matrixModuleAction U' v) =
      matrixModuleAction E₀' (matrixModuleAction T' v) := by
    rw [matrixModuleAction_mul, hET, ← matrixModuleAction_mul]
  have hfactor : matrixModuleAction E₀' (matrixModuleAction R x) = matrixModuleAction E' x := by
    rw [matrixModuleAction_mul]
    exact congrArg (fun A => matrixModuleAction A x) himage
  change matrixModuleAction E' (matrixModuleAction U' (matrixModuleAction E' x)) =
    (q : ℝ) • matrixModuleAction E' x
  rw [hact, ← hfactor]
  exact hT (matrixModuleAction R x)

theorem integerPeriod_range_le_of_columns {O K I : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [Fintype I]
    (A₀ : Matrix O K ℤ) (A : Matrix O I ℤ) (e : K → I)
    (he : ∀ i k, A i (e k) = A₀ i k) : A₀.mulVecLin.range ≤ A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨k, rfl⟩
  exact ⟨e k, funext (fun i => he i k)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem extendIntegerSiteSection_column_sum {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) (s : S) :
    (∑ i, |(extendIntegerSiteSection e T i s : ℝ)|) ≤ ∑ k, |(T k s : ℝ)| := by
  classical
  calc
    _ ≤ ∑ i : I, ∑ k : K, if e k = i then |(T k s : ℝ)| else 0 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [extendIntegerSiteSection, Int.cast_sum]
      apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    _ = ∑ k : K, ∑ i : I, if e k = i then |(T k s : ℝ)| else 0 := Finset.sum_comm
    _ = _ := by simp

theorem extendIntegerSiteSection_column_sum_bound {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) {B : ℝ} (hT : ∀ k s, |(T k s : ℝ)| ≤ B) (s : S) :
    (∑ i, |(extendIntegerSiteSection e T i s : ℝ)|) ≤ Fintype.card K * B := by
  apply (extendIntegerSiteSection_column_sum e T s).trans
  calc
    _ ≤ ∑ _k : K, B := Finset.sum_le_sum (fun k _ => hT k s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integer_section_frequency_bound {I S J : Type*} [Fintype I]
    (T : Matrix I S ℤ) (frequency : Matrix I J ℤ)
    {B C : ℝ} (hC : 0 ≤ C) (hT : ∀ s, (∑ i, |(T i s : ℝ)|) ≤ B)
    (hf : ∀ i a, |(frequency i a : ℝ)| ≤ C) (s : S) (a : J) :
    |((T.transpose * frequency) s a : ℝ)| ≤ B * C := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ i, |(T i s : ℝ) * (frequency i a : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(T i s : ℝ)| * |(frequency i a : ℝ)| := by simp only [abs_mul]
    _ ≤ ∑ i, |(T i s : ℝ)| * C :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i a) (abs_nonneg _))
    _ = (∑ i, |(T i s : ℝ)|) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ B * C := mul_le_mul_of_nonneg_right (hT s) hC

end Erdos3

end

end OAI
