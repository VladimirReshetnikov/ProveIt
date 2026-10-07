import OAI.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff

namespace OAI

section

namespace Erdos3

def ordinaryShiftBranch {N : ℕ} (h : ZMod N) (b : Fin 2) (x : ZMod N) : ℤ :=
  (if N - h.val ≤ x.val then 1 else 0) - b.val

theorem ordinaryShiftBranch_bound {N : ℕ} (h : ZMod N) (b : Fin 2) (x : ZMod N) :
    |ordinaryShiftBranch h b x| ≤ 1 := by
  have hb := b.isLt
  unfold ordinaryShiftBranch
  rw [abs_le]
  split_ifs <;> omega

theorem ordinary_shift_from_cyclic_representative {N : ℕ} [NeZero N]
    (h : ZMod N) (b : Fin 2) (x : ZMod N) :
    (x.val : ℤ) + h.val - (b.val : ℤ) * N =
      ((h + x).val : ℤ) + ordinaryShiftBranch h b x * N := by
  rw [cyclic_representative_add h x]
  unfold ordinaryShiftBranch
  split_ifs <;> ring

theorem ordinaryShiftBranch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h : ZMod N) (b : Fin 2) (x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ordinaryShiftBranch h b x = ordinaryShiftBranch h b y := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  simp only [ordinaryShiftBranch, ← hb]

end Erdos3

end

end OAI
