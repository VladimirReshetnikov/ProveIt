import OAI.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerHalving

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedSecondDifferenceInput (j : Fin 4) (x : Fin 4 → ℤ) : Fin 2 → ℤ :=
  correlationInput (x 0) (x 1 + ![0, x 2, x 3, x 2 + x 3] j)

namespace NativeMultidegreeNilcharacter

noncomputable def mixedSecondDifferenceWithShift {s : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : Fin 4 → ℤ)
    (a : (Fin M.outputDim × Fin M.outputDim) × (Fin M.outputDim × Fin M.outputDim))
    (x : Fin 4 → ℤ) : ℂ :=
  (M.eval a.1.1 (mixedSecondDifferenceInput 0 x + ![0, c 0]) *
    star (M.eval a.1.2 (mixedSecondDifferenceInput 1 x + ![0, c 1]))) *
    star (M.eval a.2.1 (mixedSecondDifferenceInput 2 x + ![0, c 2]) *
      star (M.eval a.2.2 (mixedSecondDifferenceInput 3 x + ![0, c 3])))

theorem mixedSecondDifferenceWithShift_unit {s : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : Fin 4 → ℤ) (x : Fin 4 → ℤ) :
    ∑ a, ‖M.mixedSecondDifferenceWithShift c a x‖ ^ 2 = 1 := by
  simp only [mixedSecondDifferenceWithShift, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, M.unit_eval, mul_one]

theorem exists_mixed_second_difference_translation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p) (c : Fin 4 → ℤ),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (M.mixedSecondDifferenceWithShift c) (M.mixedSecondDifferenceWithShift 0) := by
  obtain ⟨A, _, htranslate⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((V + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M c
  have hp : 0 ≤ p := (Nat.cast_nonneg M.dim).trans M.complexity.1.1
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcost : (v + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, V, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have hdegree : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  let F (j : Fin 4) : Fin 2 → ((Fin 4 → ℤ) →+ ℤ) := fun i =>
    { toFun := fun x => mixedSecondDifferenceInput j x i
      map_zero' := by fin_cases j <;> fin_cases i <;> rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change (x + y) 1 + ![0, (x + y) 2, (x + y) 3, (x + y) 2 + (x + y) 3] j =
            (x 1 + ![0, x 2, x 3, x 2 + x 3] j) +
              (y 1 + ![0, y 2, y 3, y 2 + y 3] j)
          fin_cases j <;> dsimp <;> ring }
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  have E (j : Fin 4) : NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedSecondDifferenceInput j x + ![0, c j]))
      (fun i x => M.eval i (mixedSecondDifferenceInput j x + ![0, 0])) := by
    have T := (htranslate (mixedCorrelationDegree s) hdegree M ![0, c j] 0).linearPullbackHom (F j)
    change NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedSecondDifferenceInput j x + ![0, c j]))
      (fun i x => M.eval i (mixedSecondDifferenceInput j x + 0)) at T
    simpa only [hzero] using T
  have E₀ := htensor hu (E 0) (E 1).conjugate
  have E₁ := htensor hu (E 2) (E 3).conjugate
  exact (htensor hv E₀ E₁.conjugate).mono hcost

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

def mixedSecondDifferenceHom (j : Fin 4) (i : Fin 2) : ((Fin 4 → ℤ) →+ ℤ) where
  toFun x := mixedSecondDifferenceInput j x i
  map_zero' := by fin_cases j <;> fin_cases i <;> rfl
  map_add' x y := by
    fin_cases i
    · rfl
    · change (x + y) 1 + ![0, (x + y) 2, (x + y) 3, (x + y) 2 + (x + y) 3] j =
        (x 1 + ![0, x 2, x 3, x 2 + x 3] j) + (y 1 + ![0, y 2, y 3, y 2 + y 3] j)
      fin_cases j <;> dsimp <;> ring

noncomputable def mixedSecondDifferenceVector {I : Type*} (f : I → (Fin 2 → ℤ) → ℂ)
    (a : (I × I) × (I × I)) (x : Fin 4 → ℤ) : ℂ :=
  (f a.1.1 (mixedSecondDifferenceInput 0 x) * star (f a.1.2 (mixedSecondDifferenceInput 1 x))) *
    star (f a.2.1 (mixedSecondDifferenceInput 2 x) * star (f a.2.2 (mixedSecondDifferenceInput 3 x)))

theorem NativeMultidegreeNilcharacter.mixedSecondDifferenceWithShift_zero {s : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p) :
    M.mixedSecondDifferenceWithShift 0 = mixedSecondDifferenceVector M.eval := by
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  funext a x
  simp only [NativeMultidegreeNilcharacter.mixedSecondDifferenceWithShift,
    mixedSecondDifferenceVector, Pi.zero_apply, hzero, add_zero]

theorem NativeIntegerVectorEquivalence.exists_second_difference_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (Fin 2 → ℤ) → ℂ} {g : J → (Fin 2 → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (mixedSecondDifferenceVector f) (mixedSecondDifferenceVector g) := by
  obtain ⟨A, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I J _ _ s p f g hp E
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have H (j : Fin 4) : NativeIntegerVectorEquivalence s p
      (fun i x => f i (mixedSecondDifferenceInput j x))
      (fun i x => g i (mixedSecondDifferenceInput j x)) :=
    E.linearPullbackHom (mixedSecondDifferenceHom j)
  have H₀ := htensor hp (H 0) (H 1).conjugate
  have H₁ := htensor hp (H 2) (H 3).conjugate
  have hcost : (q + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  exact (htensor hq H₀ H₁.conjugate).mono hcost

end Erdos3

end

end OAI
