import OAI.Combinatorics.Progressions.Dynamics.SlicedSourceErrorBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem exists_slicedSourceUniformAccuracy (O m : ℕ) {Pcap E F a δ : ℝ}
    (hPcap : 0 ≤ Pcap) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (ha : a⁻¹ ≤ Real.exp Pcap) (hδ : δ⁻¹ ≤ Real.exp Pcap) :
    ∃ εgrid : ℝ, 0 < εgrid ∧ εgrid ≤ 1 ∧
      εgrid⁻¹ = Real.exp (VectorPolynomial.slicedJointDensityLogBudget O m Pcap + (E + F) + 1) ∧
      ∀ (ι : Type*) [Fintype ι] (Op : ℝ),
        ∃ εlong P : ℝ, 0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp P ∧
          0 ≤ P ∧ a⁻¹ ≤ Real.exp P ∧ δ⁻¹ ≤ Real.exp P ∧ 4 ≤ Real.exp P ∧
          ∀ C : ℝ, 0 ≤ C → C ≤ Real.exp F →
            C * (Real.exp (VectorPolynomial.slicedJointDensityLogBudget O m Pcap) * εgrid +
              εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  let Qcap := VectorPolynomial.slicedJointDensityLogBudget O m Pcap
  let εgrid := Real.exp (-(Qcap + (E + F) + 1))
  have hg := slicedSourceErrorBudget (ι := Empty) O m (Op := 0)
    hPcap hE hF (Real.exp_nonneg F) le_rfl ha hδ
  refine ⟨εgrid, hg.1, hg.2.1, hg.2.2.1, ?_⟩
  intro ι hι Op
  let G := (Fintype.card ι : ℝ) * max Op 0
  let εlong := Real.exp (-(G + (E + F) + 1))
  let P := max Pcap (G + (E + F) + 2)
  obtain ⟨_, _, _, hl0, hl1, hli, hP, haP, hδP, h4, herr⟩ :=
    slicedSourceErrorBudget (ι := ι) O m (Op := Op)
      hPcap hE hF (Real.exp_nonneg F) le_rfl ha hδ
  refine ⟨εlong, P, hl0, hl1, hli, hP, haP, hδP, h4, ?_⟩
  intro C hC0 hC
  have hb : 0 ≤ Real.exp Qcap * εgrid + εlong * ∏ _i : ι, Real.exp Op := by
    exact add_nonneg (mul_nonneg (Real.exp_nonneg _) hg.1.le)
      (mul_nonneg hl0.le (Finset.prod_nonneg (fun _ _ => Real.exp_nonneg _)))
  exact (mul_le_mul_of_nonneg_right hC hb).trans herr

end Erdos3

end

end OAI
