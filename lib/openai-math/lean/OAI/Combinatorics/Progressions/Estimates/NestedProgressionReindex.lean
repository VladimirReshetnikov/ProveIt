import OAI.Combinatorics.Progressions.Geometry.CommonStrideCoordinates

namespace OAI

section

namespace Erdos3

theorem mem_integerProgressionSupport_iff_parameter (c m x : ℤ) (H : ℕ) :
    x ∈ integerProgressionSupport c m H ↔
      ∃ j : ℤ, 0 ≤ j ∧ j < H ∧ x = c + m * j := by
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    have hb := Finset.mem_Ico.mp hj
    change m * j = x - c at he
    exact ⟨j, hb.1, hb.2, by omega⟩
  · rintro ⟨j, hj0, hjH, rfl⟩
    exact ⟨j, Finset.mem_Ico.mpr ⟨hj0, hjH⟩, by simp [integerStrideHom]⟩

theorem exists_nested_progression_affine (c b : ℤ) {m d H L : ℕ}
    (hm : 0 < m) (hd : 0 < d) (hL : 0 < L)
    (hsub : integerProgressionSupport b d L ⊆ integerProgressionSupport c m H) :
    ∃ a s : ℤ, ∀ x : ℤ, 0 ≤ x → x < L →
      0 ≤ a + s * x ∧ a + s * x < H ∧ b + (d : ℤ) * x = c + m * (a + s * x) := by
  have hb := hsub (integerProgressionSupport_point b d L hd 0 hL)
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  obtain ⟨a, ha0, haH, hba⟩ := (mem_integerProgressionSupport_iff_parameter c m b H).mp hb
  by_cases hsingle : L = 1
  · refine ⟨a, 0, fun x hx0 hxL => ?_⟩
    have hx : x = 0 := by rw [hsingle] at hxL; omega
    simpa only [hx, mul_zero, add_zero] using And.intro ha0 (And.intro haH hba)
  · have hb1 := hsub (integerProgressionSupport_point b d L hd 1 (by omega))
    simp only [Nat.cast_one, mul_one] at hb1
    obtain ⟨a₁, _, _, hba₁⟩ := (mem_integerProgressionSupport_iff_parameter c m (b + d) H).mp hb1
    let s := a₁ - a
    have hs : (d : ℤ) = m * s := by dsimp [s]; nlinarith [hba, hba₁]
    refine ⟨a, s, fun x hx0 hxL => ?_⟩
    have hinner : b + (d : ℤ) * x ∈ integerProgressionSupport b d L :=
      (mem_integerProgressionSupport_iff_parameter b d _ L).mpr ⟨x, hx0, hxL, rfl⟩
    obtain ⟨j, hj0, hjH, hj⟩ := (mem_integerProgressionSupport_iff_parameter c m _ H).mp (hsub hinner)
    have hpoint : b + (d : ℤ) * x = c + m * (a + s * x) := by rw [hba, hs]; ring
    have hj' : j = a + s * x :=
      mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) (add_left_cancel (hj.symm.trans hpoint))
    exact ⟨hj' ▸ hj0, hj' ▸ hjH, hpoint⟩

end Erdos3

end

end OAI
