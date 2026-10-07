import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {S D : Type*} [Fintype S] [Fintype D] (P : D → Prop) [DecidablePred P]

noncomputable def siteDensityRestriction (x : S → D → ℝ) : (Σ _ : S × {d // ¬P d}, Unit) → ℝ :=
  fun o => x o.1.1 o.1.2.val

theorem siteDensityRestriction_lipschitz : LipschitzWith 1 (siteDensityRestriction (S := S) P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro o
  exact (dist_le_pi_dist (x o.1.1) (y o.1.1) o.1.2.val).trans (dist_le_pi_dist x y o.1.1)

theorem siteDensityRestriction_complex_lipschitz
    (f : ((Σ _ : S × {d // ¬P d}, Unit) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x : S → D → ℝ => (f (siteDensityRestriction P x) : ℂ)) := by
  have he := Complex.isometry_ofReal.lipschitzWith.comp (hf.comp (siteDensityRestriction_lipschitz P))
  simpa only [one_mul, mul_one, Function.comp_def] using he

end Erdos3

end

end OAI
