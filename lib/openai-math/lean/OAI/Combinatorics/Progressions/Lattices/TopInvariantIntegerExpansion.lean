/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.UniformFrozenDescent

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_topInvariant_integer_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = T.observable x) →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) T.eval) := by
  obtain ⟨a, _, hdescent⟩ := exists_topInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ d D w T p hp hT hinv
  let q := (p + 3) ^ 11
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + 3 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 1 ≤ 11)
  obtain ⟨n, _, Q, hQF, hQL, hQ, he, _⟩ := D.exists_controlled_top_quotient hp hT.1
  have heq : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ q := by
    intro i j
    apply (he j i).trans
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 5 ≤ 11)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, _, hS, hSe⟩ := hdescent D Q hQF hQL T q hq (hT.mono hpq) hQ heq hinv
  have hfinal : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨NativeIntegerExpansion.ofTest S (hS.mono hfinal) (fun x => (hSe x).symm)⟩

noncomputable def topInvariantIntegerExponent (s : ℕ) : ℕ :=
  (exists_topInvariant_integer_expansion.{0} s).choose

theorem topInvariant_integer_expansion {L σ : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {w : σ → ℕ}
    (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hinv : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = T.observable x) :
    Nonempty (NativeIntegerExpansion w s
      ((p + topInvariantIntegerExponent s) ^ topInvariantIntegerExponent s) T.eval) :=
  (exists_topInvariant_integer_expansion s).choose_spec.2 D T hp hT hinv

end Erdos3.RationalFilteredNilmanifold

end

end OAI
