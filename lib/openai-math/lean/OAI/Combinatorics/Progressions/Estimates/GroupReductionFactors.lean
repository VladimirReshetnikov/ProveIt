import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.Compact

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem compact_representatives_step (Γ H J : Subgroup G) {K C : Set G}
    (hK : IsCompact K) (hC : IsCompact C)
    (hreduce : ∀ g ∈ H, ∃ r ∈ K, ∃ w ∈ Γ, r⁻¹ * g * w⁻¹ ∈ J)
    (hrep : ∀ h ∈ J, ∃ c ∈ C, ∃ γ ∈ Γ, h = c * γ) :
    IsCompact (K * C) ∧ ∀ g ∈ H, ∃ c ∈ K * C, ∃ γ ∈ Γ, g = c * γ := by
  refine ⟨hK.mul hC, ?_⟩
  intro g hg
  obtain ⟨r, hr, w, hw, hrem⟩ := hreduce g hg
  obtain ⟨c, hc, γ, hγ, heq⟩ := hrep _ hrem
  refine ⟨r * c, Set.mul_mem_mul hr hc, γ * w, Γ.mul_mem hγ hw, ?_⟩
  calc
    g = r * (r⁻¹ * g * w⁻¹) * w := by group
    _ = (r * c) * (γ * w) := by rw [heq]; group

theorem exists_compact_representatives_of_reductions (Γ : Subgroup G) (H : ℕ → Subgroup G)
    (s : ℕ) (hzero : H 0 = ⊤) (hterminal : H s = ⊥)
    (hstep : ∀ i < s, ∃ K : Set G, IsCompact K ∧
      ∀ g ∈ H i, ∃ r ∈ K, ∃ w ∈ Γ, r⁻¹ * g * w⁻¹ ∈ H (i + 1)) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, ∃ c ∈ C, ∃ γ ∈ Γ, g = c * γ := by
  have haux (n : ℕ) : ∀ i, i + n = s →
      ∃ C : Set G, IsCompact C ∧ ∀ g ∈ H i, ∃ c ∈ C, ∃ γ ∈ Γ, g = c * γ := by
    induction n with
    | zero =>
      intro i hi
      have his : i = s := by omega
      subst i
      refine ⟨{1}, isCompact_singleton, ?_⟩
      intro g hg
      have hg1 : g = 1 := by simpa only [hterminal, Subgroup.mem_bot] using hg
      exact ⟨1, Set.mem_singleton 1, 1, Γ.one_mem, by simp [hg1]⟩
    | succ n ih =>
      intro i hi
      obtain ⟨C, hC, hrep⟩ := ih (i + 1) (by omega)
      obtain ⟨K, hK, hreduce⟩ := hstep i (by omega)
      exact ⟨K * C, compact_representatives_step Γ (H i) (H (i + 1)) hK hC hreduce hrep⟩
  obtain ⟨C, hC, hrep⟩ := haux s 0 (by omega)
  exact ⟨C, hC, fun g => hrep g (by simp [hzero])⟩

omit [IsTopologicalGroup G] in

theorem compactSpace_quotient_of_representatives (Γ : Subgroup G) {C : Set G}
    (hC : IsCompact C) (hrep : ∀ g : G, ∃ c ∈ C, ∃ γ ∈ Γ, g = c * γ) :
    CompactSpace (G ⧸ Γ) := by
  apply isCompact_univ_iff.mp
  have hsurj : QuotientGroup.mk '' C = (Set.univ : Set (G ⧸ Γ)) := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, γ, hγ, rfl⟩ := hrep g
    refine ⟨c, hc, ?_⟩
    apply QuotientGroup.eq.mpr
    simpa only [inv_mul_cancel_left] using hγ
  rw [← hsurj]
  exact hC.image QuotientGroup.continuous_mk

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem exists_representative_factors_of_reductions (Γ : Subgroup G)
    (H : ℕ → Subgroup G) (s : ℕ) (P : G → Prop)
    (hzero : H 0 = ⊤) (hterminal : H s = ⊥)
    (hstep : ∀ i < s, ∀ g ∈ H i,
      ∃ r, P r ∧ ∃ w ∈ Γ, r⁻¹ * g * w⁻¹ ∈ H (i + 1)) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧ (∀ r ∈ rs, P r) ∧
      ∃ γ ∈ Γ, g = rs.prod * γ := by
  have haux (n : ℕ) : ∀ i, i + n = s → ∀ g ∈ H i,
      ∃ rs : List G, rs.length = n ∧ (∀ r ∈ rs, P r) ∧
        ∃ γ ∈ Γ, g = rs.prod * γ := by
    induction n with
    | zero =>
      intro i hi g hg
      have his : i = s := by omega
      subst i
      have hg1 : g = 1 := by simpa only [hterminal, Subgroup.mem_bot] using hg
      exact ⟨[], rfl, by simp, 1, Γ.one_mem, by simpa using hg1⟩
    | succ n ih =>
      intro i hi g hg
      obtain ⟨r, hr, w, hw, hrem⟩ := hstep i (by omega) g hg
      obtain ⟨rs, hlen, hP, γ, hγ, heq⟩ := ih (i + 1) (by omega) _ hrem
      refine ⟨r :: rs, by simp [hlen], ?_, γ * w, Γ.mul_mem hγ hw, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hr
        · exact hP a ha
      · calc
          g = r * (r⁻¹ * g * w⁻¹) * w := by group
          _ = (r :: rs).prod * (γ * w) := by rw [heq, List.prod_cons]; group
  intro g
  exact haux s 0 (by omega) g (by simp [hzero])

end Erdos3

end

end OAI
