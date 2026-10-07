import OAI.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem scalarTransfer_parameter_geometry {J : Type*} [Fintype J]
    (D : ℕ) (hD : 0 < D) (anchor lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    {p L : ℝ} (hp : 2 ≤ p) (hL : 1 ≤ L) (hDlog : (D : ℝ) ≤ Real.exp p)
    (hpoint : ∀ j t, t ∈ Finset.Ico (lo j) (hi j) →
      |((anchor j + (D : ℤ) * t : ℤ) : ℝ)| ≤ Real.exp p * L) :
    ∃ R : ℕ, (∀ j, hi j - lo j ≤ (R : ℤ)) ∧
      (R : ℝ) ≤ Real.exp (5 * p) * (L * Real.exp (-(2 * p))) ∧
      (∀ j, |((anchor j + (D : ℤ) * lo j : ℤ) : ℝ) / L| ≤ Real.exp (2 * p)) ∧
      (∀ j, |((anchor j + (D : ℤ) * hi j : ℤ) : ℝ) / L| ≤ Real.exp (2 * p)) := by
  have hLpos : 0 < L := by linarith
  have hep : 2 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hDF : (D : ℝ) ≤ Real.exp p * L := hDlog.trans (le_mul_of_one_le_right (Real.exp_pos p).le hL)
  have he2 : Real.exp (2 * p) = Real.exp p * Real.exp p := by rw [← Real.exp_add]; congr 1; ring
  have hdouble : 2 * (Real.exp p * L) ≤ Real.exp (2 * p) * L := by
    rw [he2]
    nlinarith [mul_le_mul_of_nonneg_right hep (mul_nonneg (Real.exp_pos p).le hLpos.le)]
  have hend j := affineIntegerInterval_endpoint_abs D (anchor j) (lo j) (hi j) (hlen j) hDF (hpoint j)
  have hlo j : |((anchor j + (D : ℤ) * lo j : ℤ) : ℝ)| ≤ Real.exp (2 * p) * L := by
    have hf : 0 ≤ Real.exp p * L := mul_nonneg (Real.exp_pos p).le hLpos.le
    exact (hend j).1.trans ((by linarith : Real.exp p * L ≤ 2 * (Real.exp p * L)).trans hdouble)
  have hhi j : |((anchor j + (D : ℤ) * hi j : ℤ) : ℝ)| ≤ Real.exp (2 * p) * L := (hend j).2.trans hdouble
  obtain ⟨R, hR, hRbound⟩ := exists_integerBox_width_bound lo hi hlen
    (by positivity : 0 ≤ 2 * (Real.exp (2 * p) * L))
    (fun j => affineIntegerInterval_width_le D hD (anchor j) (lo j) (hi j) (hlen j) (hlo j) (hhi j))
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · have hmul : Real.exp (5 * p) * (L * Real.exp (-(2 * p))) = Real.exp (3 * p) * L := by
      calc
        _ = (Real.exp (5 * p) * Real.exp (-(2 * p))) * L := by ring
        _ = _ := by rw [← Real.exp_add, show 5 * p + -(2 * p) = 3 * p by ring]
    rw [hmul]
    have hthree : Real.exp (3 * p) = Real.exp (2 * p) * Real.exp p := by
      rw [← Real.exp_add]; congr 1; ring
    apply hRbound.trans
    rw [hthree]
    have hm := mul_le_mul_of_nonneg_right hep (mul_nonneg (Real.exp_pos (2 * p)).le hLpos.le)
    nlinarith
  · intro j
    rw [abs_div, abs_of_pos hLpos]
    exact (div_le_iff₀ hLpos).mpr (hlo j)
  · intro j
    rw [abs_div, abs_of_pos hLpos]
    exact (div_le_iff₀ hLpos).mpr (hhi j)

theorem scalarTransfer_source_endpoints (a b : ℤ) (hab : a < b)
    {p q S : ℝ} (hp : 2 ≤ p) (hq : 0 ≤ q) (hS : 1 ≤ S)
    (hpoint : ∀ t ∈ Finset.Ico a b, |(t : ℝ)| ≤ Real.exp q * S) :
    |(a : ℝ)| ≤ Real.exp (q + p) * S ∧ |(b : ℝ)| ≤ Real.exp (q + p) * S := by
  have heq : 1 ≤ Real.exp q := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hq
  have hep : 2 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hF : (1 : ℝ) ≤ Real.exp q * S := by
    simpa only [one_mul] using mul_le_mul heq hS zero_le_one (Real.exp_pos q).le
  have hend := affineIntegerInterval_endpoint_abs 1 0 a b hab (by simpa only [Nat.cast_one] using hF) (by simpa only [Nat.cast_one, Int.cast_zero, one_mul, zero_add] using hpoint)
  simp only [Nat.cast_one, one_mul, zero_add] at hend
  have htwo : 2 * (Real.exp q * S) ≤ Real.exp (q + p) * S := by
    rw [Real.exp_add]
    have hm := mul_le_mul_of_nonneg_right hep (by positivity : 0 ≤ Real.exp q * S)
    nlinarith
  exact ⟨hend.1.trans ((by linarith : Real.exp q * S ≤ 2 * (Real.exp q * S)).trans htwo), hend.2.trans htwo⟩

end Erdos3

end

end OAI
