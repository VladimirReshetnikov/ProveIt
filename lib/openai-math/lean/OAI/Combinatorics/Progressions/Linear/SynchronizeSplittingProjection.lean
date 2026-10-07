import OAI.Combinatorics.Progressions.Estimates.SplitGroupRelative

namespace OAI

section

namespace Erdos3

variable {G Q : Type*} [Group G] [Group Q]

theorem synchronize_splitting_projection (q : G →* Q) (H : Subgroup G)
    (E P R a d : G) (A D : Q) (hP : P ∈ H) (ha : a ∈ H) (hd : d ∈ H)
    (haq : q a = A⁻¹ * q E) (hdq : q d = q R * D⁻¹) :
    (E * a⁻¹) * (a * P * d) * (d⁻¹ * R) = E * P * R ∧
      a * P * d ∈ H ∧ q (E * a⁻¹) = A ∧ q (d⁻¹ * R) = D ∧
      q (a * P * d) = A⁻¹ * q (E * P * R) * D⁻¹ := by
  refine ⟨?_, H.mul_mem (H.mul_mem ha hP) hd, ?_, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, haq]
    group
  · rw [map_mul, map_inv, hdq]
    group
  · simp only [map_mul, haq, hdq]
    group

theorem exists_synchronized_splitting (q : G →* Q) (H : Subgroup G)
    (E P R : G) (A D : Q) (hP : P ∈ H)
    (hleft : A⁻¹ * q E ∈ H.map q) (hright : q R * D⁻¹ ∈ H.map q) :
    ∃ a d : G, a ∈ H ∧ d ∈ H ∧ q a = A⁻¹ * q E ∧ q d = q R * D⁻¹ ∧
      (E * a⁻¹) * (a * P * d) * (d⁻¹ * R) = E * P * R ∧
      a * P * d ∈ H ∧ q (E * a⁻¹) = A ∧ q (d⁻¹ * R) = D ∧
      q (a * P * d) = A⁻¹ * q (E * P * R) * D⁻¹ := by
  obtain ⟨a, ha, haq⟩ := hleft
  obtain ⟨d, hd, hdq⟩ := hright
  exact ⟨a, d, ha, hd, haq, hdq,
    synchronize_splitting_projection q H E P R a d A D hP ha hd haq hdq⟩

end Erdos3

end

end OAI
