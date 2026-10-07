import OAI.Combinatorics.Progressions.Geometry.CommonStrideCoordinates

namespace OAI

section

namespace Erdos3

theorem commonStridePoint_index_of_modEq {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) :
    commonStridePoint c m (commonStrideIndex c m y) = y := by
  funext i
  have hd := Int.modEq_iff_dvd.mp (hy i).symm
  change c i + (m : ℤ) * ((y i - c i) / (m : ℤ)) = y i
  rw [mul_comm, Int.ediv_mul_cancel hd]
  omega

theorem commonStrideIndex_difference {I : Type*} (c : I → ℤ) (m : ℕ) (y z : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)]) (i : I) :
    (m : ℤ) * (commonStrideIndex c m y i - commonStrideIndex c m z i) = y i - z i := by
  have hye := congrFun (commonStridePoint_index_of_modEq c m y hy) i
  have hze := congrFun (commonStridePoint_index_of_modEq c m z hz) i
  change c i + (m : ℤ) * commonStrideIndex c m y i = y i at hye
  change c i + (m : ℤ) * commonStrideIndex c m z i = z i at hze
  calc
    _ = (c i + (m : ℤ) * commonStrideIndex c m y i) -
        (c i + (m : ℤ) * commonStrideIndex c m z i) := by ring
    _ = _ := by rw [hye, hze]

theorem commonStrideIndex_period {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m)
    (q : ℕ) (y z : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)])
    (hperiod : ∀ i, ((m * q : ℕ) : ℤ) ∣ (y i - z i)) :
    ∀ i, (q : ℤ) ∣ commonStrideIndex c m y i - commonStrideIndex c m z i := by
  intro i
  apply (mul_dvd_mul_iff_left (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)).mp
  rw [commonStrideIndex_difference c m y z hy hz i]
  simpa only [Nat.cast_mul] using hperiod i

theorem commonStrideIndex_abs_difference {I : Type*} (c : I → ℤ) (m : ℕ) (y z : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)]) (i : I) :
    (m : ℝ) * |(commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ)| =
      |(y i : ℝ) - (z i : ℝ)| := by
  have he : (m : ℝ) * ((commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ)) =
      (y i : ℝ) - (z i : ℝ) := by
    exact_mod_cast commonStrideIndex_difference c m y z hy hz i
  calc
    _ = |(m : ℝ) * ((commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ))| := by
      rw [abs_mul, (show |(m : ℝ)| = (m : ℝ) from abs_of_nonneg (Nat.cast_nonneg m))]
    _ = _ := congrArg abs he

theorem commonStrideIndex_distance_le {I : Type*} (c : I → ℤ) {m : ℕ} (hm : 0 < m)
    (y z : I → ℤ) (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) (hz : ∀ i, z i ≡ c i [ZMOD (m : ℤ)])
    (A : I → ℝ) (δ : ℝ) (hdist : ∀ i, |(y i : ℝ) - (z i : ℝ)| ≤ (m : ℝ) * A i * δ) :
    ∀ i, |(commonStrideIndex c m y i : ℝ) - (commonStrideIndex c m z i : ℝ)| ≤ A i * δ := by
  intro i
  apply (mul_le_mul_iff_right₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mp
  rw [commonStrideIndex_abs_difference c m y z hy hz i]
  simpa only [mul_assoc] using hdist i

end Erdos3

end

end OAI
