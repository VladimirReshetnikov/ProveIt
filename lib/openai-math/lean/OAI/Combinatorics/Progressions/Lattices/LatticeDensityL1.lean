import OAI.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem densityDifference_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf+Kg) (fun x => |f x-g x|) := by
  simpa only [one_mul, Function.comp_def, Real.norm_eq_abs] using lipschitzWith_one_norm.comp (hf.sub hg)

theorem rectangular_density_l1_sum_le {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0) :
    (∑' k : J → ℤ, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|)/(∏ j, S j) ≤
      (∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ := by
  have hs : ∀ x, R < ‖x‖ → |f x-g x| = 0 := by
    intro x hx
    rw [hfs x hx, hgs x hx, sub_self, abs_zero]
  have he := rectangularLattice_quadrature (fun x => |f x-g x|) (densityDifference_lipschitz hf hg)
    a S hS hR hδ hδ1 hmesh hs
  have hu := (le_abs_self _).trans he
  change _ ≤ (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ at hu
  linarith

theorem rectangular_density_finite_l1_le {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (s : Finset (J → ℤ)) :
    (∑ k ∈ s, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|)/(∏ j, S j) ≤
      (∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ := by
  have hs : ∀ x, R < ‖x‖ → |f x-g x| = 0 := by
    intro x hx
    rw [hfs x hx, hgs x hx, sub_self, abs_zero]
  have hsum := rectangularWeight_summable (fun x => |f x-g x|) a S hS hs
  apply le_trans (div_le_div_of_nonneg_right
    (hsum.sum_le_tsum s (fun _ _ => abs_nonneg _)) (Finset.prod_nonneg (fun j _ => (hS j).le)))
  exact rectangular_density_l1_sum_le f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs

theorem scaled_density_l1_sum_le {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (c T : J → ℝ) {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, m/T j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0) :
    (m^Fintype.card J/(∏ j, T j)) *
      (∑' k : J → ℤ, |f (fun j => (c j+m*k j)/T j)-g (fun j => (c j+m*k j)/T j)|) ≤
      (∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ := by
  have hs : ∀ x, R < ‖x‖ → |f x-g x| = 0 := by
    intro x hx
    rw [hfs x hx, hgs x hx, sub_self, abs_zero]
  have he := scaledRectangular_quadrature (fun x => |f x-g x|) (densityDifference_lipschitz hf hg)
    c T hm hT hR hδ hδ1 hmesh hs
  have hu := (le_abs_self _).trans he
  change _ ≤ (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ at hu
  linarith

end Erdos3

end

end OAI
