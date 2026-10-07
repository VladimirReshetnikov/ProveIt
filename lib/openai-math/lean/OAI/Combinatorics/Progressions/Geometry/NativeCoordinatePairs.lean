import OAI.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_coordinate_sum_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 → ∀ {τ : Type*} [Fintype τ] (a b n : (τ → ℤ) →+ ℤ),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateConstantInput i (a x + b x) (n x)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (a x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (b x) (n x))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence bound
  refine ⟨C, hC, ?_⟩
  intro p W i hi τ _ a b n
  let A : Option σ → ((τ → ℤ) →+ ℤ) := fun j => match j with
    | none => b
    | some j => if j = i then a else n
  have hinput (x : τ → ℤ) : (fun j => A j x) = coordinatePairInput i (a x) (b x) (n x) := by
    funext j
    cases j with
    | none => rfl
    | some j =>
      by_cases hji : j = i <;> simp [A, coordinatePairInput, coordinateConstantInput, hji]
  have E := (hadd W i hi).linearPullbackHom A
  simpa only [coordinateSumVector, coordinateTensorVector, hinput,
    coordinatePairInput_sum, coordinatePairInput_left, coordinatePairInput_right] using E

theorem exists_coordinate_parallelogram_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ]
    (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 → ∀ {τ : Type*} [Fintype τ] (u v w n : (τ → ℤ) →+ ℤ),
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (v x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (w x) (n x)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateConstantInput i (u x) (n x)) *
            W.eval k.2 (coordinateConstantInput i (v x + w x - u x) (n x))) := by
  obtain ⟨a, _, hadd⟩ := exists_coordinate_sum_equivalence bound
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W i hi τ _ u v w n
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let u₄ := v + w - u
  have hu₄ (x : τ → ℤ) : u₄ x = v x + w x - u x := rfl
  have hsum (x : τ → ℤ) : u x + u₄ x = v x + w x := by rw [hu₄]; ring
  have E₁ := hadd W i hi u u₄ n
  have E₂ := hadd W i hi v w n
  have E₁' : NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) q
      (fun k x => W.eval k (coordinateConstantInput i (v x + w x) (n x)))
      (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval k.1 (coordinateConstantInput i (u x) (n x)) *
          W.eval k.2 (coordinateConstantInput i (u₄ x) (n x))) := by
    simpa only [hsum] using E₁
  have R := htrans hq E₂.symm E₁' (fun x => W.unit_eval _)
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  simpa only [hu₄] using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
