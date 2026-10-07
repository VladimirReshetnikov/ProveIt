import OAI.Combinatorics.Progressions.Lattices.IntegerFiberCount

namespace OAI

section

namespace Erdos3

noncomputable def frequencyGridInterval (M : ℕ) (center radius : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun k => |(k.val : ℝ) - center| ≤ radius)

theorem frequencyGridInterval_card (M : ℕ) (center : ℝ) {radius : ℝ} (hr : 0 ≤ radius) :
    ((frequencyGridInterval M center radius).card : ℝ) ≤ 2 * radius + 1 := by
  classical
  let A := frequencyGridInterval M center radius
  have hinj : Function.Injective (fun k : Fin M => (k.val : ℤ)) := by
    intro x y h
    exact Fin.ext (Int.ofNat_inj.mp h)
  have hc := card_integer_set_le_diameter_add_one (A.image (fun k => (k.val : ℤ)))
    (by positivity : (0 : ℝ) ≤ 2 * radius) (by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hi' := abs_le.mp (Finset.mem_filter.mp hi).2
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      push_cast
      rw [abs_le]
      constructor <;> linarith)
  simpa only [Finset.card_image_of_injective _ hinj] using hc

theorem scaled_grid_approximation {M : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ) (d : ℕ)
    {E H : ℝ} (hclose : |(k.val : ℝ) / M - (a : ℝ) / d| ≤ E) (hE : M * E ≤ H) :
    |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) - M * ((a : ℝ) / d) =
      (M : ℝ) * ((k.val : ℝ) / M - (a : ℝ) / d) := by field_simp
  rw [he, abs_mul, abs_of_pos hM']
  exact (mul_le_mul_of_nonneg_left hclose hM'.le).trans hE

theorem grid_approximation_numerator_bound {M Q H d : ℕ} (hM : 0 < M)
    (hd : 0 < d) (hdQ : d ≤ Q) (k : Fin M) (a : ℤ)
    (hclose : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |a| ≤ (Q : ℤ) * (H + 1) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdQ' : (d : ℝ) ≤ Q := by exact_mod_cast hdQ
  have hk : (k.val : ℝ) < M := by exact_mod_cast k.isLt
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hmH : (H : ℝ) ≤ M * H := le_mul_of_one_le_left hH hM'
  obtain ⟨hl, hu⟩ := abs_le.mp hclose
  have hquot : |(a : ℝ) / d| ≤ H + 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_div, abs_of_pos hd'] at hquot
  have ha := (div_le_iff₀ hd').mp hquot
  have hbound : |(a : ℝ)| ≤ (Q : ℝ) * (H + 1) :=
    ha.trans (by nlinarith)
  exact_mod_cast hbound

end Erdos3

end

end OAI
