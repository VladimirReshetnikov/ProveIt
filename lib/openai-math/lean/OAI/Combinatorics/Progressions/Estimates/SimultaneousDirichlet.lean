import Mathlib

namespace OAI

section

namespace Erdos3

noncomputable def fractionalPartBin (Q : ℕ) (hQ : 0 < Q) (x : ℝ) : Fin Q :=
  ⟨⌊(Q : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt' hQ.ne').mpr
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one x) hQR⟩

theorem fractionalPartBin_eq_error {Q : ℕ} (hQ : 0 < Q) {x y : ℝ}
    (heq : fractionalPartBin Q hQ x = fractionalPartBin Q hQ y) :
    |Int.fract x - Int.fract y| < 1 / (Q : ℝ) := by
  have hfloor : ⌊(Q : ℝ) * Int.fract x⌋₊ = ⌊(Q : ℝ) * Int.fract y⌋₊ :=
    congrArg Fin.val heq
  have hxlo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (Int.fract_nonneg x))
  have hylo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (Int.fract_nonneg y))
  have hxhi := Nat.lt_floor_add_one ((Q : ℝ) * Int.fract x)
  have hyhi := Nat.lt_floor_add_one ((Q : ℝ) * Int.fract y)
  rw [hfloor] at hxlo hxhi
  have habs : |(Q : ℝ) * (Int.fract x - Int.fract y)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [abs_mul, abs_of_pos hQR] at habs
  apply (lt_div_iff₀ hQR).mpr
  simpa only [mul_comm] using habs

theorem simultaneous_dirichlet {ι : Type*} [Fintype ι]
    (alpha : ι → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ^ Fintype.card ι ∧
      ∃ m : ι → ℤ, ∀ i, |(q : ℝ) * alpha i - m i| ≤ 1 / (Q : ℝ) := by
  classical
  let code : Fin (Q ^ Fintype.card ι + 1) → (ι → Fin Q) :=
    fun n i => fractionalPartBin Q hQ ((n.val : ℝ) * alpha i)
  have hcard : Fintype.card (ι → Fin Q) < Fintype.card (Fin (Q ^ Fintype.card ι + 1)) := by
    simp
  obtain ⟨x, y, hxy, hcode⟩ := Fintype.exists_ne_map_eq_of_card_lt code hcard
  have hordered : ∃ x y : Fin (Q ^ Fintype.card ι + 1), x < y ∧ code x = code y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, h, hcode⟩
    · exact ⟨y, x, h, hcode.symm⟩
  obtain ⟨x, y, hxy, hcode⟩ := hordered
  let q := y.val - x.val
  refine ⟨q, Nat.sub_pos_of_lt hxy, ?_,
    (fun i => ⌊(y.val : ℝ) * alpha i⌋ - ⌊(x.val : ℝ) * alpha i⌋), ?_⟩
  · exact (Nat.sub_le _ _).trans (Nat.le_of_lt_succ y.isLt)
  · intro i
    have herr := fractionalPartBin_eq_error hQ (congrFun hcode i)
    have hidentity : (q : ℝ) * alpha i -
        ((⌊(y.val : ℝ) * alpha i⌋ - ⌊(x.val : ℝ) * alpha i⌋ : ℤ) : ℝ) =
        Int.fract ((y.val : ℝ) * alpha i) - Int.fract ((x.val : ℝ) * alpha i) := by
      dsimp [q]
      rw [Nat.cast_sub hxy.le, Int.cast_sub]
      simp only [Int.fract]
      ring
    rw [hidentity, abs_sub_comm]
    exact herr.le

end Erdos3

end

end OAI
