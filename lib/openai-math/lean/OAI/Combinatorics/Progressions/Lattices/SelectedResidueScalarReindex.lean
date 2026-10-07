import OAI.Combinatorics.Progressions.Estimates.UnconditionedSmoothSlopeCap

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K I K' I' : Type*} [Fintype K] [Fintype I] [Fintype K'] [Fintype I']

theorem selectedResidueSmoothWeight_one_reindex
    (e : (K × I) ≃ (K' × I')) (W : K × I → ℝ) (W' : K' × I' → ℝ)
    (hW : ∀ i, W' (e i) = W i) (z : K × I → ℤ) :
    selectedResidueSmoothWeight (fun _ : I' => 1) {0} W' (z ∘ e.symm) =
      selectedResidueSmoothWeight (fun _ : I => 1) {0} W z := by
  simp only [selectedResidueSmoothWeight_one, rectangularWeight,
    rectangularLatticePoint_zero_origin, smoothProductProfile]
  symm
  apply Fintype.prod_equiv e
  intro i
  simp only [Function.comp_apply, e.symm_apply_apply, hW]

theorem selectedResidueSmoothMass_one_reindex
    (e : (K × I) ≃ (K' × I')) (W : K × I → ℝ) (W' : K' × I' → ℝ)
    (hW : ∀ i, W' (e i) = W i) :
    (∑' z, selectedResidueSmoothWeight (fun _ : I' => 1) {0} W' z) =
      ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} W z := by
  let E : (K × I → ℤ) ≃ (K' × I' → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  calc
    _ = ∑' z, selectedResidueSmoothWeight (fun _ : I' => 1) {0} W' (E z) :=
      (E.tsum_eq _).symm
    _ = _ := tsum_congr (fun z => selectedResidueSmoothWeight_one_reindex e W W' hW z)

end Erdos3

end

end OAI
