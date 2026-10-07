import OAI.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_integer_self_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C) W.eval W.eval := by
  obtain ⟨a, _, hadd⟩ := exists_multilinearity_equivalence (σ := σ)
  obtain ⟨c, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  let i : σ := Classical.arbitrary σ
  let A : Option σ → ((σ → ℤ) →+ ℤ) := fun j => match j with
    | none => 0
    | some k => ⟨⟨fun x => x k, rfl⟩, fun _ _ => rfl⟩
  let E := (hadd W i).linearPullbackHom A
  have hleft (k : Fin W.outputDim) (x : σ → ℤ) :
      coordinateSumVector W.eval i k (fun j => A j x) = W.eval k x := by
    simp [coordinateSumVector, coordinateAdditionInputs, A]
  have hunit (x : σ → ℤ) :
      ∑ k, ‖coordinateTensorVector W.eval i k (fun j => A j x)‖ ^ 2 = 1 :=
    coordinateTensorVector_unit W.eval W.unit_eval i _
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have F := htrans hq E E.symm hunit
  have hcost : ((p + a) ^ a + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  simpa only [hleft] using F.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
