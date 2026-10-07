import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem pointwise_normalization_error {M F Z E ε D : ℝ}
    (hZ : 1 / 2 ≤ Z) (herror : |M - F| ≤ E) (hmass : |Z - 1| ≤ ε) (hcap : |F| ≤ D) :
    |M / Z - F| ≤ 2 * E + 2 * D * ε := by
  have hZpos : 0 < Z := by linarith
  have hE : 0 ≤ E := (abs_nonneg _).trans herror
  have hε : 0 ≤ ε := (abs_nonneg _).trans hmass
  have hD : 0 ≤ D := (abs_nonneg _).trans hcap
  have he : M / Z - F = ((M - F) + F * (1 - Z)) / Z := by field_simp; ring
  rw [he, abs_div, abs_of_pos hZpos]
  have hn : |(M - F) + F * (1 - Z)| ≤ E + D * ε := by
    calc
      _ ≤ |M - F| + |F| * |1 - Z| := by simpa only [abs_mul] using abs_add_le (M - F) (F * (1 - Z))
      _ ≤ E + D * ε := add_le_add herror
        (mul_le_mul hcap (by simpa only [abs_sub_comm] using hmass) (abs_nonneg _) hD)
  calc
    _ ≤ (E + D * ε) / Z := div_le_div_of_nonneg_right hn hZpos.le
    _ ≤ 2 * E + 2 * D * ε := (div_le_iff₀ hZpos).mpr (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Z - 1) (by positivity : 0 ≤ E + D * ε)])

end Erdos3

end

end OAI
