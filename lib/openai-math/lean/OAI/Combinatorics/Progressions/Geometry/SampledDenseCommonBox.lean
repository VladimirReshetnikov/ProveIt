import OAI.Combinatorics.Progressions.Estimates.DenseSubboxCost

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_dense_common_sampled_box {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + Fintype.card I * Real.exp (-p) + ρ < α)
    (hsmall : Fintype.card I * Real.exp (-p) ≤ 1)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧ IsDenseCommonStrideBox N (p + 1) (A.image e) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) *
          (α - ε - Fintype.card I * Real.exp (-p) - ρ) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧
          2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ Fintype.card I * Real.exp (-p) ∧
          ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨A, hAn, hshape, G, j, hmass, hlocal⟩ := exists_common_sampled_box μ F S w e he hp N
    hslice hw v hv hε hρ hlarge hmean
  have hpos : 0 < μ.mass G := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (by linarith)) hmass
  have hGn : G.Nonempty := by
    by_contra h
    have hz : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz, FiniteProbabilityWeights.mass, Finset.sum_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨z, hz⟩ := hGn
  refine ⟨A, hAn, ?_, G, j, hmass, hlocal⟩
  apply (hslice z (j z)).of_large_subbox hshape (Finset.image_subset_image (hlocal z hz).1)
  simpa only [Finset.card_image_of_injective _ he] using ((hlocal z hz).2.1.trans hsmall)

theorem exists_dense_common_sampled_box_of_seminorm {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α : ℝ} (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card I * Real.exp (-p) ≤ α / 8)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧ IsDenseCommonStrideBox N (p + 1) (A.image e) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧ α / 4 ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨A, hAn, hAdense, G, j, hmass, hlocal⟩ := exists_dense_common_sampled_box μ F S w
    e he hp N hslice hw v hv (show 0 < α / 8 by positivity) (show 0 ≤ α / 4 by positivity)
    (show α / 8 + Fintype.card I * Real.exp (-p) + α / 4 < α by linarith)
    (show Fintype.card I * Real.exp (-p) ≤ 1 by linarith) hmean
  refine ⟨A, hAn, hAdense, G, j, ?_, fun z hz => ⟨(hlocal z hz).1, (hlocal z hz).2.2⟩⟩
  exact (mul_le_mul_of_nonneg_left (by linarith : α / 2 ≤
    α - α / 8 - Fintype.card I * Real.exp (-p) - α / 4) (Real.exp_nonneg _)).trans hmass

end Erdos3

end

end OAI
