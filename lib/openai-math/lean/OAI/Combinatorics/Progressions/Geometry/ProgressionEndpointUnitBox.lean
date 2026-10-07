import OAI.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily

namespace OAI

section

namespace Erdos3

theorem progression_slice_endpoint_unit_box {S step H : ℕ} (c : ℤ)
    (hS : 0 < S) (hstep : 0 < step) (hH : 0 < H)
    (hcontained : integerProgressionSupport c (step : ℤ) H ⊆
      Finset.Ico (0 : ℤ) (S : ℤ)) :
    0 ≤ (c : ℝ) / S ∧
      0 ≤ (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S ∧
      (c : ℝ) / S + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S ≤ 1 := by
  have hfirst := hcontained (integerProgressionSupport_point c step H hstep 0 hH)
  have hlast := hcontained (integerProgressionSupport_point c step H hstep
    (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have he : (0 : ℤ) ≤ c := by simpa using (Finset.mem_Ico.mp hfirst).1
    exact_mod_cast he
  have hend : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < S := by
    exact_mod_cast (Finset.mem_Ico.mp hlast).2
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  refine ⟨div_nonneg hc hSreal.le, by positivity, ?_⟩
  rw [← add_div]
  exact (div_le_one hSreal).mpr hend.le

end Erdos3

end

end OAI
