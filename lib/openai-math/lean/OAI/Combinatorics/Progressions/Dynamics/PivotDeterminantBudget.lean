import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
import OAI.Combinatorics.Progressions.Linear.MatrixSupInverse

namespace OAI

section

namespace Erdos3

theorem integerPivot_det_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {H : ℝ} (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    (A.det.natAbs : ℝ) ≤ (Fintype.card I).factorial * H ^ Fintype.card I := by
  have hd : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have h := matrix_det_abs_le_uniform_bound (A.map (Int.castRingHom ℝ)) hA
  rw [hd] at h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

theorem integerPivot_polynomial_period_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {C L : ℝ} (h : ℕ)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h) :
    (A.det.natAbs : ℝ) ≤
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * Fintype.card I) := by
  have hb := integerPivot_det_bound A hA
  simpa only [mul_pow, ← pow_mul, mul_assoc] using hb

end Erdos3

end

end OAI
