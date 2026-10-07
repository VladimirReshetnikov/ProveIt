/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.UnitVerticalDifference

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem HasUniformLowerRankUnitFamily.mono {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype I] {s r d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {R : D.DegreeRankStructure (r + 1)} {v : I → D.Space → ℂ} {w : σ → ℕ}
    {p q : ℝ} (h : HasUniformLowerRankUnitFamily D R v w p) (hpq : p ≤ q) :
    HasUniformLowerRankUnitFamily D R v w q := by
  obtain ⟨n, hn, Q, S, hS, hK⟩ := h
  refine ⟨n, hn, Q, S, hS.mono S hpq, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, (fun i => (hKc i).mono hpq), hKu, a, ha0, hKe⟩

namespace UnitVerticalObservable

universe u v w t

theorem exists_uniform_lower_rank_difference_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type u} {I : Type v} {J : Type w} {σ : Type t}
      [LieRing L] [LieAlgebra ℚ L]
      [Fintype I] [Fintype J]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
      (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      (U : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) J p),
      0 ≤ p → R.ComplexityLE p →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = U.frequency x) →
      ∀ w : σ → ℕ,
        HasUniformLowerRankUnitFamily D R (V.differenceObservable U) w ((p + C) ^ C) := by
  let a := (exists_lower_rank_family.{u, max v w, t} s).choose
  let P : Polynomial ℕ := (Polynomial.X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L I J σ _ _ _ _ _ _ _ _ r d D R p V U hp hR hfreq w
  have hb : (p + 2 + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have h := hasUniformLowerRankUnitFamily D R (rankDifference R V U hfreq) w
    (by linarith) (hR.mono R (by linarith)) (fun _ _ => rfl)
  exact h.mono hb

end UnitVerticalObservable
end Erdos3.RationalFilteredNilmanifold

end

end OAI
