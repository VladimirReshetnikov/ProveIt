import OAI.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_parametric_quarter_torus_extension
    {Y D : Type*} [PseudoMetricSpace Y] [Fintype D]
    (F : Y × (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hL : LipschitzWith L F) (hB : ∀ p, ‖F p‖ ≤ B) :
    ∃ g : Y × (D → AddCircle (1 : ℝ)) → ℂ,
      LipschitzWith (2 * L) g ∧ (∀ z, ‖g z‖ ≤ 2 * B) ∧
      ∀ y (v : D → ℝ), (∀ i, |v i| ≤ 1 / 4) →
        g (y, fun i => (v i : AddCircle (1 : ℝ))) = F (y, v) := by
  let Q : Set (Y × (D → AddCircle (1 : ℝ))) := {p | ∀ i, ‖p.2 i‖ ≤ 1 / 4}
  let H : Y × (D → AddCircle (1 : ℝ)) → ℂ := fun p => F (p.1, centeredTorusLift p.2)
  have hH : LipschitzOnWith L H Q := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hc : dist (centeredTorusLift x.2) (centeredTorusLift y.2) ≤ dist x.2 y.2 := by
      simpa only [NNReal.coe_one, one_mul] using centeredTorusLift_lipschitzOn.dist_le_mul x.2 hx y.2 hy
    have hp : dist (x.1, centeredTorusLift x.2) (y.1, centeredTorusLift y.2) ≤ dist x y :=
      max_le_max le_rfl hc
    exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hp L.coe_nonneg)
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_bounded_lipschitz_extension H Q L B hH
    (fun p _ => hB (p.1, centeredTorusLift p.2))
  refine ⟨g, hg, hgb, ?_⟩
  intro y v hv
  have hQ : (y, fun i => (v i : AddCircle (1 : ℝ))) ∈ Q := by
    intro i
    rw [norm_eq_abs_centeredCircleLift, centeredCircleLift_coe (hv i)]
    exact hv i
  rw [← heq hQ]
  apply congrArg F
  apply Prod.ext
  · rfl
  · funext i
    exact centeredCircleLift_coe (hv i)

end Erdos3

end

end OAI
