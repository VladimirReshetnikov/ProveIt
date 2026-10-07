import OAI.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget

namespace OAI

section

namespace Erdos3

open Module

theorem heightBoundedSubspaces_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedSubspaces e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedSubspaces e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

theorem exists_common_height_bounded_subspace_family
    {α ι κ L : Type*} [Fintype ι] [Fintype κ] [AddCommGroup L] [Module ℚ L]
    (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty)
    (K : α → κ → Submodule ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, ∀ k, K a k ∈ heightBoundedSubspaces e m ⌈Real.exp A⌉₊) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2)) * Fintype.card κ) * S.card ≤
        (T.card : ℝ) := by
  classical
  let C := heightBoundedSubspaces e m ⌈Real.exp A⌉₊
  let : Fintype C := (finite_card_heightBoundedSubspaces e m ⌈Real.exp A⌉₊).1.fintype
  have hcard : Fintype.card C = C.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcount : (Fintype.card C : ℝ) ≤ Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
    rw [hcard]
    exact heightBoundedSubspaces_ncard_exp_bound e m hA
  obtain ⟨labels, T, hsub, hnonempty, hsize, hconst⟩ := exists_large_fixed_choices S hS
    (fun a k (u : C) => K a k = u.val)
    (fun a ha k => ⟨⟨K a k, hK a ha k⟩, rfl⟩) hcount
  obtain ⟨a₀, ha₀⟩ := hnonempty
  refine ⟨a₀, hsub ha₀, T, hsub, ha₀, ?_, hsize⟩
  intro a ha
  funext k
  exact (hconst a ha k).trans (hconst a₀ ha₀ k).symm

end Erdos3

end

end OAI
