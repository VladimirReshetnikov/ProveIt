import OAI.Combinatorics.Progressions.Estimates.CyclicOrdinaryShiftBranches

namespace OAI

section

namespace Erdos3

theorem ordinary_shift_path_dist_le {X : Type*} [PseudoMetricSpace X]
    (P : ℤ → X) {N : ℕ} [NeZero N] (h : ZMod N) (b : Fin 2) (x y : ZMod N)
    {ρ δ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hcircle : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hobs : ∀ t : ℤ, |t| ≤ 1 →
      dist (P (((h + x).val : ℤ) + t * N)) (P (((h + y).val : ℤ) + t * N)) ≤ δ) :
    dist (P ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
      (P ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ δ := by
  have hb := ordinaryShiftBranch_eq_of_good_circle h b x y hρ hx hy hcircle
  rw [ordinary_shift_from_cyclic_representative h b x,
    ordinary_shift_from_cyclic_representative h b y, ← hb]
  exact hobs _ (ordinaryShiftBranch_bound h b x)

theorem positive_cell_ordinary_shift_recovery {I J X : Type*} [PseudoMetricSpace X]
    {N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (P : ℤ → X) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ i x, 0 ≤ A i x)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hobs : ∀ j x y, 0 < B j x → 0 < B j y → ∀ t : ℤ, |t| ≤ 1 →
      dist (P ((x.val : ℤ) + t * N)) (P ((y.val : ℤ) + t * N)) ≤ δ)
    (h : ZMod N) (b : Fin 2) (i : I) (j : J) (x y : ZMod N)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h)) :
    dist (P ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
      (P ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ δ := by
  have hpos (z : ZMod N) (hz : 0 < A i z * B j (z + h)) : 0 < A i z ∧ 0 < B j (z + h) := by
    rcases mul_pos_iff.mp hz with h | h
    · exact h
    · linarith [hA i z]
  obtain ⟨hAx, hBx⟩ := hpos x hxy
  obtain ⟨hAy, hBy⟩ := hpos y hyy
  apply ordinary_shift_path_dist_le P h b x y hρ hx hy (hcircle i x y hAx hAy)
  intro t ht
  simpa only [add_comm h x, add_comm h y] using hobs j (x + h) (y + h) hBx hBy t ht

end Erdos3

end

end OAI
