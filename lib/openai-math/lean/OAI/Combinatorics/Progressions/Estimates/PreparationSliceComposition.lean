import OAI.Combinatorics.Progressions.Linear.RankPreparationSizes

namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

@[simp] theorem identity_point (x : ∀ i, Fin (N i)) : (identity N).point x = x := by
  ext i
  simp [identity, point]

noncomputable def integerPolynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℤ :=
  MvPolynomial.C (S.start i : ℤ) + MvPolynomial.C (q : ℤ) * MvPolynomial.X i

theorem integerPolynomial_degree (S : ResidueBoxSlice N q) (i : I) :
    (S.integerPolynomial i).totalDegree ≤ 1 := by
  dsimp only [integerPolynomial]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, zero_le]
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

@[simp] theorem integerPolynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℤ) (fun i => ((x i).val : ℤ)) (S.integerPolynomial i) =
      ((S.point x i).val : ℤ) := by
  simp [integerPolynomial, point, Nat.cast_add, Nat.cast_mul]

noncomputable def reindexInteger (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ) : MvPolynomial I ℤ :=
  MvPolynomial.aeval (R := ℤ) S.integerPolynomial P

theorem reindexInteger_degree (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ) {d : ℕ}
    (hP : P.totalDegree ≤ d) : (S.reindexInteger P).totalDegree ≤ d := by
  exact (aeval_polynomial_totalDegree_le P S.integerPolynomial hP S.integerPolynomial_degree).trans_eq
    (Nat.mul_one d)

@[simp] theorem reindexInteger_eval (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ)
    (x : ∀ i, Fin (S.length i)) :
    MvPolynomial.eval (fun i => ((x i).val : ℤ)) (S.reindexInteger P) =
      MvPolynomial.eval (fun i => ((S.point x i).val : ℤ)) P := by
  change MvPolynomial.aeval (R := ℤ) (fun i => ((x i).val : ℤ))
    (MvPolynomial.aeval (R := ℤ) S.integerPolynomial P) = _
  rw [MvPolynomial.comp_aeval_apply]
  simp only [integerPolynomial_eval, MvPolynomial.aeval_eq_eval]

end ResidueBoxSlice

namespace RankPreparationFamily

theorem compose_slice_identity {I J : Type} [Fintype I] [DecidableEq J] {s : ℕ}
    {L L' L'' : RankPreparationFamily I J s} {N : I → ℕ} {q r : ℕ}
    (S : ResidueBoxSlice N q) (T : ResidueBoxSlice S.length r)
    (ip ip' : J → MvPolynomial I ℤ) (c c' : J → ℝ)
    (err : (∀ i, Fin (S.length i)) → J → ℝ) (err' : (∀ i, Fin (T.length i)) → J → ℝ)
    (hS : ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
      L'.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j)
    (hT : ∀ x j, L'.value (fun i => ((T.point x i).val : ℝ)) j =
      L''.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip' j) : ℝ) + c' j + err' x j) :
    ∀ x j, L.value (fun i => (((S.comp T).point x i).val : ℝ)) j =
      L''.value (fun i => ((x i).val : ℝ)) j +
      (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (T.reindexInteger (ip j) + ip' j) : ℝ) +
      (c j + c' j) + (err (T.point x) j + err' x j) := by
  intro x j
  change (∀ i, Fin (T.length i)) at x
  rw [ResidueBoxSlice.comp_point, hS, hT, map_add, Int.cast_add, ResidueBoxSlice.reindexInteger_eval]
  ring

end RankPreparationFamily
end Erdos3

end

end OAI
